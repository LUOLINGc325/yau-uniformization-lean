import Yau.Blueprint.Alignment

/-! The projection inverse grows at most linearly in the actual macro index. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem projection_inverse_scale {q eps B j : ℝ} (hq : 0 < q) (heps : 0 < eps)
    (hB : 0 ≤ B) (hj : 1 ≤ j) :
    Real.sqrt (2 * (B * q + eps * q / j ^ 2) / (eps * q / j ^ 2)) ≤
      Real.sqrt (2 * (B + eps) / eps) * j := by
  have hjpos : 0 < j := by linarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have hratio : 2 * (B * q + eps * q / j ^ 2) / (eps * q / j ^ 2) ≤
      (2 * (B + eps) / eps) * j ^ 2 := by
    field_simp
    have hpay := mul_le_mul_of_nonneg_left hj2 heps.le
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (B + eps) / eps), Real.sqrt_sq hjpos.le] at hsqrt
  exact hsqrt

theorem perturbation_threshold_scale {q eps B j δ : ℝ} (hq : 0 < q) (_heps : 0 < eps)
    (hB : 0 < B) (hj : 0 < j) (hδ : δ ≤ eps / (64 * B * j ^ 2)) :
    32 * δ * (B * q) ≤ (eps * q / j ^ 2) / 2 := by
  have hpay := (le_div_iff₀ (by positivity : 0 < 64 * B * j ^ 2)).1 hδ
  have hmul := mul_le_mul_of_nonneg_right hpay hq.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  apply (le_div_iff₀ (sq_pos_of_pos hj)).2
  nlinarith

end Yau.Blueprint.Alignment.Y03Proof
