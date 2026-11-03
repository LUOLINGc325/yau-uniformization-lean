import Yau.Geometry.Basic

open scoped Topology RealInnerProductSpace ENNReal
open MeasureTheory Set Filter Metric

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

/-- The squared norm submean inequality on a circle, including zero-dimensional targets. -/
theorem holomorphic_circle_norm_sq_mean {q : ℕ}
    (F : ℂ → ComplexVector q) {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    (z : ℂ) (a : ℝ) (ha : 0 < a) (hball : closedBall z a ⊆ U) :
    ‖F z‖ ^ 2 ≤ Real.circleAverage (fun w => ‖F w‖ ^ 2) z a := by
  have hc : ContinuousOn F (sphere z a) :=
    hF.continuousOn.mono (sphere_subset_closedBall.trans hball)
  have hmean : Real.circleAverage F z a = F z := by
    have hd : DiffContOnCl ℂ F (ball z |a|) := by
      simpa only [abs_of_pos ha] using hF.diffContOnCl_ball hball
    exact hd.circleAverage
  let L : ComplexVector q →L[ℝ] ℝ := innerSL ℝ (F z)
  have hLcont : ContinuousOn (fun w => L (F w)) (sphere z a) := L.continuous.comp_continuousOn hc
  have hi : CircleIntegrable F z a := hc.circleIntegrable ha.le
  have hL : Real.circleAverage (fun w => L (F w)) z a = ‖F z‖ ^ 2 := by
    have h := L.circleAverage_comp_comm hi
    simpa [Function.comp_def, hmean, L, innerSL_apply_apply] using h
  have hN : CircleIntegrable (fun w => ‖F w‖ ^ 2) z a := (hc.norm.pow 2).circleIntegrable ha.le
  have h2L : CircleIntegrable (fun w => 2 * L (F w)) z a :=
    (continuousOn_const.mul hLcont).circleIntegrable ha.le
  have hsub : CircleIntegrable (fun w => ‖F w‖ ^ 2 - 2 * L (F w)) z a :=
    ((hc.norm.pow 2).sub (continuousOn_const.mul hLcont)).circleIntegrable ha.le
  have hconst : CircleIntegrable (fun _ : ℂ => ‖F z‖ ^ 2) z a :=
    continuousOn_const.circleIntegrable ha.le
  have hnonneg : 0 ≤ Real.circleAverage (fun w => ‖F w - F z‖ ^ 2) z a :=
    Real.circleAverage_nonneg_of_nonneg (fun _ _ => sq_nonneg _)
  have he : (fun w : ℂ => ‖F w - F z‖ ^ 2) =
      fun w => (‖F w‖ ^ 2 - 2 * L (F w)) + ‖F z‖ ^ 2 := by
    funext w
    simpa only [L, innerSL_apply_apply, real_inner_comm] using norm_sub_sq_real (F w) (F z)
  rw [he, Real.circleAverage_fun_add hsub hconst, Real.circleAverage_fun_sub hN h2L,
    show Real.circleAverage (fun w => 2 * L (F w)) z a =
      2 * Real.circleAverage (fun w => L (F w)) z a from
        (by simpa only [smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := (2 : ℝ)) (f := fun w => L (F w)) (c := z) (R := a))),
    hL, Real.circleAverage_const] at hnonneg
  linarith

end Yau.Proofs.D03Aux
