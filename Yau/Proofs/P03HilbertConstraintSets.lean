import Yau.Proofs.P03HilbertSolutionSet

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

/-- A regularized norm bound is imposed on the same fixed-source solution
slice in the same fixed genuine Hilbert space. -/
def regularizedHilbertConstraint (f : WeightedOneSection E g μ hμ h hh Φ hΦ)
    (T : WeightedTopHilbert E g μ hμ h hh Φ hΦ →L[ℂ] WeightedTopHilbert E g μ hμ h hh Φ hΦ)
    (R : ℝ) : Set (WeightedTopHilbert E g μ hμ h hh Φ hΦ) :=
  fixedSourceSolutionSet E g μ hμ h hh Φ hΦ f ∩ T ⁻¹' Metric.closedBall 0 R

theorem regularizedHilbertConstraint_isClosed (f : WeightedOneSection E g μ hμ h hh Φ hΦ)
    (T : WeightedTopHilbert E g μ hμ h hh Φ hΦ →L[ℂ] WeightedTopHilbert E g μ hμ h hh Φ hΦ)
    (R : ℝ) : IsClosed (regularizedHilbertConstraint E g μ hμ h hh Φ hΦ f T R) :=
  (fixedSourceSolutionSet_isClosed E g μ hμ h hh Φ hΦ f).inter
    (Metric.isClosed_closedBall.preimage T.continuous)

theorem regularizedHilbertConstraint_convex (f : WeightedOneSection E g μ hμ h hh Φ hΦ)
    (T : WeightedTopHilbert E g μ hμ h hh Φ hΦ →L[ℂ] WeightedTopHilbert E g μ hμ h hh Φ hΦ)
    (R : ℝ) : Convex ℝ (regularizedHilbertConstraint E g μ hμ h hh Φ hΦ f T R) :=
  (fixedSourceSolutionSet_convex E g μ hμ h hh Φ hΦ f).inter
    ((convex_closedBall (0 : WeightedTopHilbert E g μ hμ h hh Φ hΦ) R).linear_preimage
      (T.restrictScalars ℝ).toLinearMap)

theorem regularizedHilbertConstraint_mem_iff (f : WeightedOneSection E g μ hμ h hh Φ hΦ)
    (T : WeightedTopHilbert E g μ hμ h hh Φ hΦ →L[ℂ] WeightedTopHilbert E g μ hμ h hh Φ hΦ)
    (R : ℝ) (v : WeightedTopHilbert E g μ hμ h hh Φ hΦ) :
    v ∈ regularizedHilbertConstraint E g μ hμ h hh Φ hΦ f T R ↔
      WeakDbar (r := r) E (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v).1 f.1 ∧
        ‖T v‖ ≤ R := by
  change (v ∈ fixedSourceSolutionSet E g μ hμ h hh Φ hΦ f ∧ T v ∈ Metric.closedBall 0 R) ↔ _
  rw [fixedSourceSolutionSet_mem_iff, Metric.mem_closedBall, dist_zero_right]

end Yau.NodeProofs.P03Aux
