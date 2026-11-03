import Yau.LeafProofs.L14
import Mathlib.Analysis.Convex.Basic

open scoped Manifold Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]
variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
  (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)

/-- The affine slice of the already proved actual maximal dbar graph with
one fixed source in the same fixed weighted Hilbert realization. -/
def fixedSourceSolutionSet (f : WeightedOneSection E g μ hμ h hh Φ hΦ) :
    Set (WeightedTopHilbert E g μ hμ h hh Φ hΦ) :=
  {v | (v, realizeWeightedOneSection E g μ hμ h hh Φ hΦ f) ∈
    weightedMaximalDbarHilbertGraph E g μ hμ h hh Φ hΦ}

theorem fixedSourceSolutionSet_mem_iff (f : WeightedOneSection E g μ hμ h hh Φ hΦ)
    (v : WeightedTopHilbert E g μ hμ h hh Φ hΦ) :
    v ∈ fixedSourceSolutionSet E g μ hμ h hh Φ hΦ f ↔
      WeakDbar (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v).1 f.1 := by
  have he := weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh Φ hΦ
    (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v) f
  simpa only [weightedTopHilbertRepresentative_realize, fixedSourceSolutionSet, Set.mem_setOf_eq] using he

theorem fixedSourceSolutionSet_isClosed (f : WeightedOneSection E g μ hμ h hh Φ hΦ) :
    IsClosed (fixedSourceSolutionSet E g μ hμ h hh Φ hΦ f) :=
  (weightedMaximalDbarHilbertGraph_isClosed E g μ hμ h hh Φ hΦ).preimage
    (continuous_id.prodMk continuous_const)

theorem fixedSourceSolutionSet_convex (f : WeightedOneSection E g μ hμ h hh Φ hΦ) :
    Convex ℝ (fixedSourceSolutionSet E g μ hμ h hh Φ hΦ f) := by
  let S := weightedMaximalDbarHilbertGraph E g μ hμ h hh Φ hΦ
  let H := WeightedTopHilbert E g μ hμ h hh Φ hΦ
  let F := realizeWeightedOneSection E g μ hμ h hh Φ hΦ f
  let A : H →ᵃ[ℝ] H × WeightedOneHilbert E g μ hμ h hh Φ hΦ :=
    (AffineMap.id ℝ H).prod (AffineMap.const ℝ H F)
  have hs : Convex ℝ (S : Set (H × WeightedOneHilbert E g μ hμ h hh Φ hΦ)) :=
    (S.restrictScalars ℝ).convex
  exact hs.affine_preimage A

end Yau.NodeProofs.P03Aux
