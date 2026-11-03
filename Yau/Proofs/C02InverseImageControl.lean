import Yau.Proofs.C02QuantitativeInverseSmooth
import Mathlib.Analysis.Calculus.MeanValue

/-! The fixed inverse chart has a quantitative position estimate on the
same receiving ball. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_position_bound_on_receiving_ball
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
    (r : ℝ) (hr : 0 ≤ r)
    (hReceiving : Metric.closedBall (e 0) r ⊆ e.target)
    (hSmooth : ContDiffOn ℝ ∞ e.symm e.target)
    (hDeriv : ∀ y ∈ e.target, ‖fderiv ℝ e.symm y‖ ≤ 2)
    (y : E) (hy : y ∈ Metric.closedBall (e 0) r) :
    ‖e.symm y‖ ≤ 2 * ‖y - e 0‖ := by
  have hDiff (z : E) (hz : z ∈ Metric.closedBall (e 0) r) :
      DifferentiableAt ℝ e.symm z :=
    ((hSmooth z (hReceiving hz)).contDiffAt (e.open_target.mem_nhds (hReceiving hz))).differentiableAt (by simp)
  have hh := (convex_closedBall (e 0) r).norm_image_sub_le_of_norm_fderiv_le
    hDiff (fun z hz => hDeriv z (hReceiving hz)) (Metric.mem_closedBall_self hr) hy
  rw [e.left_inv he0, sub_zero] at hh
  exact hh

end Yau.Blueprint.C02Proof
