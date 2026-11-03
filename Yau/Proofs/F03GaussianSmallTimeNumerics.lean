import Yau.Proofs.F03HeatInterpolation

/-! The genuine off-diagonal Gaussian beats the exact small-ball polynomial loss at time zero. -/
noncomputable section
open Filter
open scoped Topology
namespace Yau.Proofs.F03Aux

theorem inv_pow_mul_exp_neg_div_tendsto_zero (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b : ℝ => (b⁻¹)^m*Real.exp (-a/b)) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
    (tendsto_inv_nhdsGT_zero.const_mul_atTop ha)).const_mul ((a⁻¹)^m)
  simp only [mul_zero] at h
  convert h using 1
  funext b
  simp only [Function.comp_def,div_eq_mul_inv,mul_pow,neg_mul]
  have hCancel : (a⁻¹)^m*a^m=1 := by rw [← mul_pow,inv_mul_cancel₀ ha.ne',one_pow]
  calc
    _ = ((a⁻¹)^m*a^m)*((b⁻¹)^m*Real.exp (-a*b⁻¹)) := by simp only [hCancel,one_mul,neg_mul]
    _ = _ := by simp only [neg_mul];ring

theorem small_time_gaussian_split {c r d b : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hrd : r ≤ d) (hb : 0 < b) (hb1 : b ≤ 1) :
    Real.exp (-c*d^2/b) ≤ Real.exp (-(c*r^2/2)/b)*Real.exp (-(c/2)*d^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hSq : r^2 ≤ d^2 := pow_le_pow_left₀ hr hrd 2
  apply (mul_le_mul_iff_of_pos_right hb).mp
  field_simp
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hSq),
    mul_nonneg (mul_nonneg hc (sq_nonneg d)) (sub_nonneg.mpr hb1)]

end Yau.Proofs.F03Aux
