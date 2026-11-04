# yau-uniformization-lean

A Lean 4 formalization of Theorem 1.1 of the paper
**"Uniformization of complete Kähler manifolds with positive bisectional curvature"**
(OpenAI Math Release preprint, September 23, 2026), the uniformization statement conjectured by Yau.
The proof relies only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

[![build](https://github.com/LUOLINGc325/yau-uniformization-lean/actions/workflows/build.yml/badge.svg)](https://github.com/LUOLINGc325/yau-uniformization-lean/actions/workflows/build.yml)
Reproduce: see [`.github/workflows/build.yml`](.github/workflows/build.yml).

> **Attribution.** The mathematics (theorem and proof) is that of the paper. This repository is an *independent*
> Lean 4 formalization, written by AI coding agents under the direction of the repository owner (LUOLINGc325).
> It is not affiliated with or endorsed by the paper's authors.

## What is formalized

Theorem 1.1: every complete, connected, noncompact Kähler manifold of complex dimension `n ≥ 1` with positive
holomorphic bisectional curvature is biholomorphic to `ℂⁿ`.

| Lean name | Content |
|---|---|
| `Yau.main` | Theorem 1.1 |
| `Yau.main_nonvacuous` | the hypotheses are satisfiable in complex dimension 1: `Nonempty (KahlerManifold 1)` (the complete cigar metric on `ℂ`) |

The statements are in [`spec/STATEMENT.lean`](spec/STATEMENT.lean); every definition they use is in
[`Yau/Geometry/Basic.lean`](Yau/Geometry/Basic.lean). The proof is assembled in `Yau/Proofs/MainEndpoint.lean`.

```lean
theorem main {n : ℕ} (hn : 1 ≤ n) (X : KahlerManifold n) :
    BiholomorphicToComplexEuclidean X.manifold

theorem main_nonvacuous : Nonempty (KahlerManifold 1)
```

Reading notes (the Lean kernel certifies that the proofs prove *these* statements; whether the definitions
match the paper is for the reader to judge):
- `ComplexManifold n`: an arbitrary carrier type with a Mathlib `ChartedSpace` over `EuclideanSpace ℂ (Fin n)` that
  is an analytic manifold for the model `𝓘(ℂ, ℂⁿ)` (holomorphic transition maps), Hausdorff, second countable,
  connected and noncompact.
- `KahlerManifold n`: a complex manifold with a Hermitian metric whose chart coefficients are `C^∞`, whose induced
  length distance (infimum of lengths of piecewise-`C¹` curves) is complete (every Cauchy sequence converges), whose Kähler form is closed, and which
  satisfies the paper's curvature hypothesis `Rm(u,v,v,u) + Rm(u,Jv,Jv,u) > 0` for all nonzero real tangent vectors
  `u, v` (`PaperPositiveBisectional`). The curvature tensor is computed from the metric's Levi-Civita symbols; it is
  not supplied as data. Only `PaperPositiveBisectional` enters `KahlerManifold`; the other curvature definitions in
  `Basic.lean` (a Chern-curvature calculator and normalization lemmas) are not used by the statement.
- `SmoothMetric` also records, as fields, distance laws and the chart-transition rule of the Hermitian field;
  `smoothMetric_of_complete_field` (`Yau/Proofs/C04BoundedGeometryChartsMetric.lean`) builds a `SmoothMetric` from
  smoothness, the Kähler condition and completeness alone, so these fields add no hypothesis.
- `BiholomorphicToComplexEuclidean M`: there is a Mathlib `Diffeomorph` (complex model `𝓘(ℂ, ℂⁿ)`, smoothness `⊤`)
  from `M` onto the standard `ℂⁿ` that is holomorphic with holomorphic inverse (smooth with ℂ-linear derivative
  everywhere, in both directions). The carrier of `M` is arbitrary.
- `main_nonvacuous` is proved in `Yau/Witness/` from the metric `(dx² + dy²)/(1 + |z|²)` on `ℂ`. Non-vacuity is
  machine-checked only for `n = 1`; the definitions are uniform in `n`.
- Comments in some development modules (for example under `spec/attacks/` and `spec/CHAIN/`) describe earlier planning
  states ("unproved", "open assumptions"); they are historical. `Yau/Proofs/MainEndpoint.lean` supplies every premise
  of the endpoint assembly with proved theorems, and the axiom check below confirms that nothing is assumed.
  Comments citing `spec/paper/…` refer to the development copy of the paper, which is not included (see `NOTICE`).

## Verification

The [build workflow](.github/workflows/build.yml) of this repository checks out the tree, fetches Mathlib from its
official cache, runs `lake build`, and fails on any `sorry` warning or error in the build log. It scans the sources
(comments and strings removed) for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom`
declarations, `@[csimp]`, `debug.` options, and commands that add declarations or run code during elaboration
(`macro`, `syntax`, `elab`, `initialize`, `run_cmd`, `#eval`, …). It checks that `Yau/Geometry/Basic.lean` has the
SHA-256 recorded in [`scripts/DEFINITIONS.sha256`](scripts/DEFINITIONS.sha256) (the file reviewed before release),
elaborates [`scripts/CheckStatement.lean`](scripts/CheckStatement.lean), which checks that both endpoints have the
stated types (up to definitional unfolding), and checks with `#print axioms` that they depend only on `propext`,
`Classical.choice` and `Quot.sound`.

A full build exceeds the 6-hour limit of one hosted job. A run therefore saves the project build (`.lake/build`)
under a key derived from the SHA-256 of all Lean sources, the lakefile, the lockfile and the toolchain, and a later
run restores only a build made from byte-identical sources. Lake then rebuilds nothing that is up to date and
replays the stored build logs, so their warnings (including `sorry`) are still checked. While building, the workflow
deletes the per-module setup files of modules that Lake has finished (`scripts/prune_setups.py`), which would
otherwise fill the runner's disk.

The Lean files are the import closure of `spec/STATEMENT.lean` in commit `1b328a4c0a783c23d79288eeb00a58df995fe364`
of a private development repository (7543 files, byte-identical); `lakefile.toml` is regenerated to list exactly
these modules. Development notes, unused modules and internal tooling are not included. Toolchain
`leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

## Building

```sh
lake exe cache get
lake build
lake env lean scripts/CheckStatement.lean
```

A full build compiles 7543 project modules and takes many hours.

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`).

## License

Apache-2.0, see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).

發自我的手機
