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
| `Yau.main_nonvacuous` | the hypotheses are satisfiable: `Nonempty (KahlerManifold 1)` (the complete cigar metric on `ℂ`) |

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
  not supplied as data.
- `BiholomorphicToComplexEuclidean M`: there is a Mathlib `Diffeomorph` (complex model `𝓘(ℂ, ℂⁿ)`, smoothness `⊤`)
  from `M` onto the standard `ℂⁿ` that is holomorphic with holomorphic inverse (smooth with ℂ-linear derivative
  everywhere, in both directions). The carrier of `M` is arbitrary.
- `main_nonvacuous` is proved in `Yau/Witness/` from the metric `(dx² + dy²)/(1 + |z|²)` on `ℂ`.

## Verification

The [build workflow](.github/workflows/build.yml) of this repository builds every module from a clean checkout
(Mathlib from its official cache), fails on any `sorry` warning or error, scans the sources (comments and strings
removed) for `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom` declarations and
`debug.` options, checks that `Yau/Geometry/Basic.lean` is byte-identical to the audited file
([`scripts/DEFINITIONS.sha256`](scripts/DEFINITIONS.sha256)), checks the exact types of both endpoints
([`scripts/CheckStatement.lean`](scripts/CheckStatement.lean)) and that they depend only on `propext`,
`Classical.choice` and `Quot.sound`.

Before this release, development commit `1b328a4c0a783c23d79288eeb00a58df995fe364` passed the development
acceptance process: a full build, `#print axioms Yau.main` = `[propext, Classical.choice, Quot.sound]`,
no source axioms or `sorry`, and an independent adversarial final review of the statement, the definitions and the
proof modules. Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

This repository contains the import closure of `spec/STATEMENT.lean` from that commit (7543 Lean files,
byte-identical), plus `README.md`, `LICENSE`, `NOTICE`, `.gitignore`, `scripts/` and `.github/`; `lakefile.toml` lists exactly these
modules. Development notes, unused modules and internal tooling are not included. The build workflow of this repository passed on this tree.

## Building

```sh
lake exe cache get
lake build
lake env lean scripts/CheckStatement.lean
```

A full build compiles 7543 project modules and can take several hours; the workflow caches the project build, so a
run stopped by the time limit can be re-run and continues where it stopped.

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`).

## License

Apache-2.0, see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).

發自我的手機
