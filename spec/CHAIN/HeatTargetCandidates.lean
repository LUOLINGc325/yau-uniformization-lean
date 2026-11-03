import spec.CHAIN.LeafCandidates

/-!
Statement proposals for the already registered fixed-metric F03 producers.
These are output predicates, not construction theorems. In particular the
bounded-initial-face predicate must be applied to the SAME minimal kernel
produced upstream; no arbitrary kernel is asserted to satisfy it here.
The domain/exhaustion and canonical Hilbert realization APIs needed to state
all six full producer targets are not supplied by this module.
-/
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
noncomputable section
namespace Yau.HeatTargetCandidates
open Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual integral against the unchanged Riemannian measure. At time zero
use the prescribed datum, rather than a function-valued delta kernel.
The values at negative times carry no condition in the heat class. -/
def boundedKernelEvolution (μ : Measure M.Carrier)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) (f : M.Carrier → ℝ)
    (b : ℝ) (x : M.Carrier) : ℝ :=
  if b = 0 then f x else ∫ y, H b x y * f y ∂μ

/-- Positive-time output fragment of WP03-F03-MINIMAL-EXHAUSTION.
This does not assert minimality, exhaustion convergence or construction.
`g` is the same computed complex Laplacian field and `μ` the same volume
throughout; their geometric provenance is an upstream obligation. -/
def MinimalKernelPositiveTimeOutput (g : HermitianField M) (μ : Measure M.Carrier)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  LeafCandidates.ScalarHeatKernel g μ H ∧
  (∀ x y, ContDiffOn ℝ ∞
    (fun p : (ComplexVector n × ComplexVector n) × ℝ =>
      H p.2 (chartInv x p.1.1) (chartInv y p.1.2))
    ((chartTarget x ×ˢ chartTarget y) ×ˢ Set.Ioi 0)) ∧
  (∀ b, 0 < b → ∀ x, Integrable (H b x) μ ∧
    0 ≤ (∫ y, H b x y ∂μ) ∧ (∫ y, H b x y ∂μ) ≤ 1) ∧
  ∀ b c, 0 < b → 0 < c → ∀ x y,
    Integrable (fun z => H b x z * H c z y) μ ∧
    H (b + c) x y = ∫ z, H b x z * H c z y ∂μ

/-- Exact output predicate of WP03-F03-BOUNDED-INITIAL-FACE for the SAME H
already produced by the minimal-exhaustion node. No kernel property, solution,
representation, conservation or regularity conclusion is an input here.
The input class has no global derivative bounds. The existing
`IsBoundedScalarHeat` includes ALL compact-chart spatial initial jets. -/
def BoundedInitialFaceOutput (g : HermitianField M) (μ : Measure M.Carrier)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  ∀ f : M.Carrier → ℝ, SmoothFn f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∀ b, 0 < b → ∀ x, Integrable (fun y => H b x y * f y) μ) ∧
    (∀ B : ℝ, 0 ≤ B → (∀ y, |f y| ≤ B) → ∀ b, 0 < b → ∀ x,
      (∫ y, |H b x y * f y| ∂μ) ≤ B ∧
      |boundedKernelEvolution μ H f b x| ≤ B) ∧
    IsBoundedScalarHeat g f (boundedKernelEvolution μ H f)

end Yau.HeatTargetCandidates
