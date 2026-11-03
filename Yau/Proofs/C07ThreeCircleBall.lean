import Yau.Proofs.C07ThreeCircle

namespace Yau.Proofs.C07Aux

open Set

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Three-circle interpolation on the entire middle closed ball, including
its center and the points inside the inner ball. -/
theorem three_circle_exp_bound {f : E → G} {R l u x a b : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hlu : l < u) (huR : Real.exp u < R) (hx : x ∈ Icc l u)
    (hab : a ≤ b)
    (hinner : ∀ z : E, ‖z‖ ≤ Real.exp l → ‖f z‖ ≤ Real.exp a)
    (houter : ∀ z : E, ‖z‖ ≤ Real.exp u → ‖f z‖ ≤ Real.exp b)
    {z : E} (hz : ‖z‖ ≤ Real.exp x) :
    ‖f z‖ ≤ Real.exp (a * (1 - (x - l) / (u - l)) + b * ((x - l) / (u - l))) := by
  have hd : 0 < u - l := sub_pos.mpr hlu
  have hα : 0 ≤ (x - l) / (u - l) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  by_cases hzi : ‖z‖ ≤ Real.exp l
  · apply (hinner z hzi).trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hα]
  · have hzn : 0 < ‖z‖ := (Real.exp_pos l).trans (lt_of_not_ge hzi)
    let y := Real.log ‖z‖
    have hly : l ≤ y := (Real.le_log_iff_exp_le hzn).2 (le_of_not_ge hzi)
    have hyx : y ≤ x := (Real.log_le_iff_le_exp hzn).2 hz
    have hyu : y ≤ u := hyx.trans hx.2
    let v : E := (‖z‖ : ℂ)⁻¹ • z
    have hv : ‖v‖ = 1 := by
      simp [v, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ hzn.ne']
    have hrepr : (Real.exp y : ℂ) • v = z := by
      rw [Real.exp_log hzn]
      simp [v, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hzn.ne')]
    have hline := three_circle_on_line hf hlu huR ⟨hly, hyu⟩ hv
      (fun w hw => hinner w hw.le) houter
    rw [hrepr, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add] at hline
    apply hline.trans
    apply Real.exp_le_exp.mpr
    have hαxy : (y - l) / (u - l) ≤ (x - l) / (u - l) :=
      div_le_div_of_nonneg_right (sub_le_sub_right hyx l) hd.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hαxy)]

end Yau.Proofs.C07Aux
