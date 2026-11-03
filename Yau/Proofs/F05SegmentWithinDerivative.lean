import Mathlib

/-! The segment FTC identity realizes the one-sided spatial derivative on a
convex physical set, including its genuine boundary. -/

open Set Filter MeasureTheory Asymptotics
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem F05_hasFDerivWithinAt_of_segment_integral {S : Set E} (hS : Convex ℝ S)
    {f : E → F} {G : E → E →L[ℝ] F} {x : E} (hx : x ∈ S)
    (hG : ContinuousWithinAt G S x)
    (hInt : ∀ y ∈ S, IntervalIntegrable (fun r : ℝ => G (AffineMap.lineMap x y r)) volume 0 1)
    (hFTC : ∀ y ∈ S,
      f y - f x = (∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r)) (y-x)) :
    HasFDerivWithinAt f (G x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO,isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hGD⟩ := Metric.continuousWithinAt_iff.mp hG ε hε
  have hBall : Metric.ball x δ ∈ 𝓝[S] x :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)
  filter_upwards [self_mem_nhdsWithin,hBall] with y hy hyδ
  have hyNorm : ‖y-x‖ < δ := by simpa only [Metric.mem_ball,dist_eq_norm] using hyδ
  have hNear (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      ‖G (AffineMap.lineMap x y r) - G x‖ ≤ ε := by
    have hLine : AffineMap.lineMap x y r - x = r • (y-x) := by
      simp only [AffineMap.lineMap_apply_module',add_sub_cancel_right]
    have hDist : dist (AffineMap.lineMap x y r) x < δ := by
      rw [dist_eq_norm,hLine,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1]
      exact (mul_le_of_le_one_left (norm_nonneg (y-x)) hr.2).trans_lt hyNorm
    have hGN : ‖G (AffineMap.lineMap x y r) - G x‖ < ε := by
      simpa only [dist_eq_norm] using hGD (hS.lineMap_mem hx hy hr) hDist
    exact hGN.le
  have hIntegral : ‖(∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r)) - G x‖ ≤ ε := by
    have hSub : (∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r)) - G x =
        ∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r) - G x := by
      rw [intervalIntegral.integral_sub (hInt y hy) intervalIntegrable_const]
      simp
    rw [hSub]
    have hBound : ‖∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r) - G x‖ ≤ ε * |1-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro r hr
        have hr' : r ∈ Ioc (0 : ℝ) 1 := by
          simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
        exact hNear r ⟨hr'.1.le,hr'.2⟩)
    simpa using hBound
  rw [hFTC y hy]
  change ‖((∫ r in (0 : ℝ)..1, G (AffineMap.lineMap x y r)) - G x) (y-x)‖ ≤ ε * ‖y-x‖
  exact (ContinuousLinearMap.le_opNorm _ (y-x)).trans
    (mul_le_mul_of_nonneg_right hIntegral (norm_nonneg (y-x)))

end Yau.Proofs.F05Aux
