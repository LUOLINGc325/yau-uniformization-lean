import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The scalar consequence of the source's fixed-power static distortion estimate. -/

noncomputable section

namespace Yau.Proofs.C04Aux

theorem distortion_log_bound (n : ℕ) (D m M ρ : ℝ) (hD : 0 < D)
    (hm : 1 ≤ m) (hM : 0 < M)
    (hdet : Real.exp ρ ≤ M ^ n)
    (hdist : Real.sqrt M ≤ D * (1 + Real.sqrt m) ^ D) :
    ρ ≤ (n : ℝ) * (2 * Real.log D + 2 * D * Real.log 2 + D * Real.log m) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hsqrt : 1 ≤ Real.sqrt m := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hm
  have hdetlog := Real.log_le_log (Real.exp_pos ρ) hdet
  rw [Real.log_exp, Real.log_pow] at hdetlog
  have hdistlog := Real.log_le_log (Real.sqrt_pos.mpr hM) hdist
  rw [Real.log_mul hD.ne' (ne_of_gt (Real.rpow_pos_of_pos (by positivity) D)),
    Real.log_rpow (by positivity)] at hdistlog
  rw [Real.sqrt_eq_rpow M, Real.log_rpow hM] at hdistlog
  have hsum : Real.log (1 + Real.sqrt m) ≤ Real.log 2 + (1 / 2 : ℝ) * Real.log m := by
    have hh := Real.log_le_log (show 0 < 1 + Real.sqrt m by positivity)
      (show 1 + Real.sqrt m ≤ 2 * Real.sqrt m by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.sqrt_pos.mpr hmpos).ne',
      Real.sqrt_eq_rpow m, Real.log_rpow hmpos] at hh
    simpa only [Real.sqrt_eq_rpow] using hh
  have hMlog : Real.log M ≤ 2 * Real.log D + 2 * D * Real.log 2 + D * Real.log m := by
    have hh := mul_le_mul_of_nonneg_left hsum hD.le
    nlinarith
  exact hdetlog.trans (mul_le_mul_of_nonneg_left hMlog (Nat.cast_nonneg n))

theorem distortion_exponential_lower (n : ℕ) (D m M ρ s : ℝ) (hn : 0 < n)
    (hD : 0 < D) (hm : 1 ≤ m) (hM : 0 < M)
    (hdet : Real.exp ρ ≤ M ^ n)
    (hdist : Real.sqrt M ≤ D * (1 + Real.sqrt m) ^ D)
    (hrho : s / 2 ≤ ρ)
    (hs : 4 * |(n : ℝ) * (2 * Real.log D + 2 * D * Real.log 2)| ≤ s) :
    Real.exp (((4 * (n : ℝ) * D)⁻¹) * s) ≤ m := by
  have hlog := distortion_log_bound n D m M ρ hD hm hM hdet hdist
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < 4 * (n : ℝ) * D := by positivity
  have hA : (n : ℝ) * (2 * Real.log D + 2 * D * Real.log 2) ≤ s / 4 := by
    linarith [le_abs_self ((n : ℝ) * (2 * Real.log D + 2 * D * Real.log 2))]
  have hmlog : ((4 * (n : ℝ) * D)⁻¹) * s ≤ Real.log m := by
    rw [mul_comm ((4 * (n : ℝ) * D)⁻¹) s, ← div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    Real.exp (((4 * (n : ℝ) * D)⁻¹) * s) ≤ Real.exp (Real.log m) := Real.exp_le_exp.mpr hmlog
    _ = m := Real.exp_log (zero_lt_one.trans_le hm)

end Yau.Proofs.C04Aux
