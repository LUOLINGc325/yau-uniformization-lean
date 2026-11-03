import Yau.Proofs.D03PlanarArea

open scoped Topology ENNReal
open MeasureTheory Set Filter Metric

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

theorem holomorphic_norm_sq_le_l2 {q : ℕ} (F : ℂ → ComplexVector q) {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hL2 : (∫⁻ w in U, ENNReal.ofReal (‖F w‖ ^ 2) ∂volume) < ⊤)
    (z : ℂ) (a : ℝ) (ha : 0 < a) (hball : closedBall z a ⊆ U) :
    ‖F z‖ ^ 2 ≤ (Real.pi * a ^ 2)⁻¹ *
      (∫⁻ w in U, ENNReal.ofReal (‖F w‖ ^ 2) ∂volume).toReal := by
  have h := (holomorphic_area_mean F hU hF z a ha hball).trans
    (lintegral_mono_set (ball_subset_closedBall.trans hball))
  have hr := (ENNReal.ofReal_le_iff_le_toReal hL2.ne).1 h
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos ha))).2
  simpa only [mul_comm] using hr

theorem holomorphic_norm_le_sqrt_l2 {q : ℕ} (F : ℂ → ComplexVector q) {U : Set ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hL2 : (∫⁻ w in U, ENNReal.ofReal (‖F w‖ ^ 2) ∂volume) < ⊤)
    (z : ℂ) (a : ℝ) (ha : 0 < a) (hball : closedBall z a ⊆ U) :
    ‖F z‖ ≤ Real.sqrt ((Real.pi * a ^ 2)⁻¹ *
      (∫⁻ w in U, ENNReal.ofReal (‖F w‖ ^ 2) ∂volume).toReal) :=
  Real.le_sqrt_of_sq_le (holomorphic_norm_sq_le_l2 F hU hF hL2 z a ha hball)

/-- Area L² convergence of holomorphic maps implies convergence of every derivative at the center. -/
theorem holomorphic_l2_iteratedDeriv_tendsto {q : ℕ} (R : ℝ) (hR : 0 < R)
    (F : ℂ → ComplexVector q) (Fn : ℕ → ℂ → ComplexVector q)
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (hFn : ∀ n, DifferentiableOn ℂ (Fn n) (ball 0 R))
    (hfinite : ∀ n, (∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) < ⊤)
    (hconv : Tendsto (fun n => ∫⁻ z in ball (0 : ℂ) R,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) atTop (𝓝 0)) :
    ∀ j : ℕ, Tendsto (fun n => iteratedDeriv j (Fn n) 0) atTop (𝓝 (iteratedDeriv j F 0)) := by
  let mass : ℕ → ℝ≥0∞ := fun n => ∫⁻ z in ball (0 : ℂ) R,
    ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume
  let B : ℕ → ℝ := fun n => Real.sqrt ((Real.pi * (R / 4) ^ 2)⁻¹ * (mass n).toReal)
  have hmass : Tendsto (fun n => (mass n).toReal) atTop (𝓝 0) := by
    simpa only [mass, Function.comp_def, ENNReal.toReal_zero] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B, Function.comp_def, mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (hmass.const_mul (Real.pi * (R / 4) ^ 2)⁻¹)
  have hdiff (n : ℕ) : DifferentiableOn ℂ (fun z => Fn n z - F z) (ball 0 R) := (hFn n).sub hF
  have hsphere (n : ℕ) (z : ℂ) (hz : z ∈ sphere 0 (R / 2)) : ‖Fn n z - F z‖ ≤ B n := by
    apply holomorphic_norm_le_sqrt_l2 _ isOpen_ball (hdiff n) (hfinite n) z (R / 4) (by positivity)
    intro w hw
    have ht := dist_triangle w z (0 : ℂ)
    have hw' := mem_closedBall.mp hw
    have hz' := mem_sphere.mp hz
    simp only [dist_zero_right] at ht hz'
    rw [mem_ball_zero_iff]
    linarith
  intro j
  have hfcont : ContDiffAt ℂ j F 0 :=
    ((hF.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))).of_le le_top
  have hbound (n : ℕ) :
      ‖iteratedDeriv j (Fn n) 0 - iteratedDeriv j F 0‖ ≤ (j.factorial : ℝ) * B n / (R / 2) ^ j := by
    have hncont : ContDiffAt ℂ j (Fn n) 0 :=
      (((hFn n).contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))).of_le le_top
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by positivity : 0 < R / 2)
      ((hdiff n).diffContOnCl_ball (closedBall_subset_ball (by linarith : R / 2 < R))) (hsphere n)
    simpa only [iteratedDeriv_fun_sub hncont hfcont] using hc
  have hlim : Tendsto (fun n => (j.factorial : ℝ) * B n / (R / 2) ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (hB.const_mul (j.factorial : ℝ)).div_const ((R / 2) ^ j)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hbound hlim)

end Yau.Proofs.D03Aux
