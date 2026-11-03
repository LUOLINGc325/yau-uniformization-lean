import spec.CHAIN.CONTRACTS

/-! The single low-order radius and the absorption coefficient for every
radial jet order. These numbers depend only on the supplied curvature bound. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

def radialGaugeRadius (K : ℝ) : ℝ := (4 * Real.sqrt (1 + K))⁻¹

theorem radialGaugeRadius_pos {K : ℝ} (hK : 0 ≤ K) : 0 < radialGaugeRadius K := by
  unfold radialGaugeRadius
  positivity

theorem radialGaugeRadius_sq {K : ℝ} (hK : 0 ≤ K) :
    radialGaugeRadius K ^ 2 = (16 * (1 + K))⁻¹ := by
  have hs : (Real.sqrt (1 + K)) ^ 2 = 1 + K := Real.sq_sqrt (by linarith)
  dsimp only [radialGaugeRadius]
  simp only [mul_inv, mul_pow, inv_pow, hs]
  norm_num

theorem curvature_mul_radialGaugeRadius_sq {K : ℝ} (hK : 0 ≤ K) :
    K * radialGaugeRadius K ^ 2 ≤ 1 / 16 := by
  rw [radialGaugeRadius_sq hK]
  have hDen : 0 < 16 * (1 + K) := by positivity
  rw [← div_eq_mul_inv, div_le_iff₀ hDen]
  linarith

theorem radialGaugeRadius_le_quarter {K : ℝ} (hK : 0 ≤ K) :
    radialGaugeRadius K ≤ 1 / 4 := by
  have hs : (1 : ℝ) ≤ Real.sqrt (1 + K) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hp := radialGaugeRadius_pos hK
  have hm : radialGaugeRadius K * (4 * Real.sqrt (1 + K)) = 1 :=
    inv_mul_cancel₀ (by positivity)
  nlinarith

theorem radial_top_coefficient_le {K : ℝ} (hK : 0 ≤ K) (m : ℕ) (hm : 1 ≤ m) :
    3 * K * radialGaugeRadius K ^ 2 / ((m : ℝ) + 2) ^ 2 ≤ 1 / 48 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hDen : 0 < ((m : ℝ) + 2) ^ 2 := by positivity
  rw [div_le_iff₀ hDen]
  have hSmall := curvature_mul_radialGaugeRadius_sq hK
  nlinarith [sq_nonneg ((m : ℝ) + 2 - 3)]

theorem radial_two_inequality_absorption
    (α β c d q L f a : ℝ) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hTop : c ^ 2 * q ≤ 1 / 2)
    (hα : α ≤ c * (q * β + L) + d * f)
    (hβUpper : β ≤ c * α + d * a) :
    β ≤ 2 * (c ^ 2 * L + c * d * f + d * a) := by
  have hCombined := hβUpper.trans
    (add_le_add (mul_le_mul_of_nonneg_left hα hc) (le_refl (d * a)))
  have hCoefficient := mul_le_mul_of_nonneg_right hTop hβ
  nlinarith

end Yau.Blueprint.C02Proof
