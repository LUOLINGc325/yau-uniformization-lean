#!/usr/bin/env python3
"""Prune successful Lake setup JSON files safely while a build is running."""
from __future__ import annotations

import argparse
import json
import os
import shutil
import stat
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

SETUP_SUFFIX = ".setup.json"
BUILD = Path(".lake/build")
IR = BUILD / "ir"
LIB_LEAN = BUILD / "lib" / "lean"


@dataclass
class SweepResult:
    deleted: int = 0
    deleted_bytes: int = 0
    kept: int = 0


def now_utc() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log_error(exc: BaseException) -> None:
    msg = f"{type(exc).__name__}: {exc}".replace("\n", " ").replace("\r", " ")
    print(f"prune error {now_utc()}: {msg[:300]}", flush=True)


def setup_stem(setup: Path) -> str | None:
    try:
        rel = setup.relative_to(IR)
    except ValueError:
        return None
    name = rel.name
    if not name.endswith(SETUP_SUFFIX):
        return None
    stem_name = name[:-len(SETUP_SUFFIX)]
    if not stem_name:
        return None
    try:
        return rel.with_name(stem_name).as_posix()
    except ValueError:
        return None


def signature(path: Path):
    st = path.lstat()
    if not stat.S_ISREG(st.st_mode):
        raise ValueError("not a regular file")
    return (st.st_ino, st.st_size, st.st_mtime_ns), st


def cmdline_readers(target_abs: str) -> tuple[bool, bool]:
    needle = os.fsencode(target_abs)
    try:
        entries = list(Path("/proc").iterdir())
    except OSError:
        return False, True
    for proc in entries:
        if not proc.name.isdigit():
            continue
        try:
            data = (proc / "cmdline").read_bytes()
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError:
            try:
                comm = (proc / "comm").read_text(encoding="utf-8", errors="replace").strip()
            except (FileNotFoundError, ProcessLookupError):
                continue
            except OSError:
                return False, True
            if comm in ("lean", "lake", "leanir"):
                return False, True
            continue
        except OSError:
            continue
        if needle in data:
            return True, False
    return False, False


def check_artifact(parent: Path, stem: str, description: str) -> bool:
    if not isinstance(description, str) or not description or "." not in description:
        return False
    digest, ext = description.split(".", 1)
    if not digest or not ext:
        return False
    artifact = parent / (stem + "." + ext)
    try:
        st = artifact.stat()
    except OSError:
        return False
    if not stat.S_ISREG(st.st_mode) or artifact.is_symlink() or st.st_size <= 0:
        return False
    sidecar = artifact.with_name(artifact.name + ".hash")
    try:
        sst = sidecar.stat()
        if not stat.S_ISREG(sst.st_mode) or sidecar.is_symlink():
            return False
        text = sidecar.read_text(encoding="utf-8").strip()
    except (OSError, UnicodeError):
        return False
    return text == digest


def try_delete(setup: Path, stem: str) -> tuple[bool, int]:
    try:
        setup_sig, st = signature(setup)
        trace_path = LIB_LEAN / (stem + ".trace")
        try:
            tst = trace_path.stat()
        except OSError:
            return False, 0
        if not stat.S_ISREG(tst.st_mode) or trace_path.is_symlink():
            return False, 0
        if tst.st_mtime_ns < st.st_mtime_ns:
            return False, 0

        try:
            trace = json.loads(trace_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError):
            return False, 0
        if not isinstance(trace, dict):
            return False, 0
        if trace.get("synthetic") is not False:
            return False, 0

        log = trace.get("log")
        if not isinstance(log, list):
            return False, 0
        for entry in log:
            if not isinstance(entry, dict):
                return False, 0
            if entry.get("level") == "error":
                return False, 0

        outputs = trace.get("outputs")
        if not isinstance(outputs, dict):
            return False, 0
        for key, parent in (("o", LIB_LEAN), ("i", LIB_LEAN), ("c", IR)):
            if key not in outputs:
                return False, 0
            value = outputs[key]
            if isinstance(value, str):
                if not value:
                    return False, 0
                descriptions = [value]
            elif isinstance(value, list):
                if not value:
                    return False, 0
                descriptions = value
            else:
                return False, 0
            for desc in descriptions:
                if not check_artifact(parent, stem, desc):
                    return False, 0

        setup_abs = os.path.abspath(os.fspath(setup))
        used, unknown = cmdline_readers(setup_abs)
        if used or unknown:
            return False, 0

        new_sig, new_st = signature(setup)
        if new_sig != setup_sig:
            return False, 0
        if not stat.S_ISREG(new_st.st_mode):
            return False, 0
        setup.unlink()
        return True, st.st_size
    except (OSError, ValueError, KeyError, TypeError):
        return False, 0


def sweep() -> SweepResult:
    res = SweepResult()
    if not IR.is_dir():
        return res
    try:
        setups = list(IR.rglob("*.setup.json"))
    except OSError as exc:
        log_error(exc)
        return res

    for setup in setups:
        stem = setup_stem(setup)
        if stem is None:
            res.kept += 1
            continue
        try:
            deleted, size = try_delete(setup, stem)
        except Exception:
            deleted, size = False, 0
        if deleted:
            res.deleted += 1
            res.deleted_bytes += size
        else:
            res.kept += 1
    return res


def print_line(res: SweepResult, total_count: int, total_bytes: int) -> None:
    mb = res.deleted_bytes / (1024.0 ** 2)
    total_gb = total_bytes / (1024.0 ** 3)
    try:
        free_gb = shutil.disk_usage(".").free / (1024.0 ** 3)
        free_s = f"{free_gb:.2f}"
    except OSError:
        free_s = "?"
    print(
        f"prune {now_utc()}: deleted {res.deleted} ({mb:.1f} MB); "
        f"total {total_count} ({total_gb:.2f} GB); kept {res.kept}; free {free_s} GB",
        flush=True,
    )


def run_loop(interval: float, stop_file: Path | None) -> None:
    total_count = 0
    total_bytes = 0
    last_print = time.monotonic()
    while True:
        if stop_file is not None and stop_file.exists():
            return
        try:
            res = sweep()
        except Exception as exc:
            log_error(exc)
            res = SweepResult()

        total_count += res.deleted
        total_bytes += res.deleted_bytes
        now = time.monotonic()
        if res.deleted > 0 or now - last_print >= 600:
            print_line(res, total_count, total_bytes)
            last_print = now

        if stop_file is not None and stop_file.exists():
            return

        wait = max(0.0, float(interval))
        end = time.monotonic() + wait
        while True:
            if stop_file is not None and stop_file.exists():
                return
            remaining = end - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(remaining, 1.0))
            if time.monotonic() - last_print >= 600:
                print_line(SweepResult(), total_count, total_bytes)
                last_print = time.monotonic()


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--loop", type=float, default=None, metavar="SECONDS")
    parser.add_argument("--stop-file", type=Path, default=None)
    args = parser.parse_args(argv)

    if args.loop is not None:
        run_loop(args.loop, args.stop_file)
        return 0

    try:
        res = sweep()
    except Exception as exc:
        log_error(exc)
        res = SweepResult()
    print_line(res, res.deleted, res.deleted_bytes)
    return 0


if __name__ == "__main__":
    sys.exit(main())
