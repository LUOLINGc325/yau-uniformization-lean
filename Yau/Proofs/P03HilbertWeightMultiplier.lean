import Yau.Proofs.P03PoleMultipliers
import Yau.LeafProofs.L14TopChartApprox

open scoped Manifold Topology ContDiff
open MeasureTheory

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

/-- A regularized weight is implemented by an actual bounded multiplier
on one fixed genuine weighted Hilbert space. -/
def poleHilbertMultiplier (p : M.Carrier → ℝ) (hp : SmoothFn p)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, poleMultiplier p x ^ 2 ≤ C ^ 2) :
    WeightedTopHilbert E g μ hμ h hh Φ hΦ →L[ℂ] WeightedTopHilbert E g μ hμ h hh Φ hΦ :=
  weightedTopMultiplier E g μ hμ h hh Φ hΦ (poleMultiplier p) (poleMultiplier_smooth p hp) C hC hbound

/-- Exact change of weight for the same actual top-form representative. -/
theorem multiply_top_weight_identity (p : M.Carrier → ℝ) (u : NQForm E 0) :
    weightedNormSq (r := r) E g.form h μ Φ
      (multiplyForm E (fun x => (poleMultiplier p x : ℂ)) u) =
      weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p x) u := by
  apply lintegral_congr
  intro x
  rw [formNormSq_multiply_real_top]
  apply congrArg ENNReal.ofReal
  calc
    poleMultiplier p x ^ 2 * BundleDbar.formNormSq (r := r) E g.form h u x * Real.exp (-Φ x) =
        BundleDbar.formNormSq (r := r) E g.form h u x *
          (poleMultiplier p x ^ 2 * Real.exp (-Φ x)) := by ring
    _ = _ := by rw [poleMultiplier_sq_weight]

theorem poleHilbertMultiplier_normSq (p : M.Carrier → ℝ) (hp : SmoothFn p)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, poleMultiplier p x ^ 2 ≤ C ^ 2)
    (v : WeightedTopHilbert E g μ hμ h hh Φ hΦ) :
    ENNReal.ofReal (‖poleHilbertMultiplier E g μ hμ h hh Φ hΦ p hp C hC hbound v‖ ^ 2) =
      weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p x)
        (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v).1 := by
  let U := weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v
  let V := weightedTopMultiplierSection E g μ hμ h hh Φ hΦ
    (poleMultiplier p) (poleMultiplier_smooth p hp) C hC hbound U
  have ht : poleHilbertMultiplier E g μ hμ h hh Φ hΦ p hp C hC hbound v =
      realizeWeightedTopSection E g μ hμ h hh Φ hΦ V := by
    calc
      _ = weightedTopMultiplier E g μ hμ h hh Φ hΦ
          (poleMultiplier p) (poleMultiplier_smooth p hp) C hC hbound
          (realizeWeightedTopSection E g μ hμ h hh Φ hΦ U) := by
        rw [weightedTopHilbertRepresentative_realize]
        rfl
      _ = _ := weightedTopMultiplier_realize E g μ hμ h hh Φ hΦ
        (poleMultiplier p) (poleMultiplier_smooth p hp) C hC hbound U
  have hnorm : ‖poleHilbertMultiplier E g μ hμ h hh Φ hΦ p hp C hC hbound v‖ = ‖V‖ := by
    rw [ht]
    exact UniformSpace.Completion.norm_coe V
  calc
    _ = weightedNormSq (r := r) E g.form h μ Φ V.1 := by
      rw [weightedTopSection_normSq_eq_ofReal, hnorm]
    _ = _ := multiply_top_weight_identity E g μ h Φ p U.1

end Yau.NodeProofs.P03Aux
