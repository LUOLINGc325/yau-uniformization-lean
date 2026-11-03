import Yau.Proofs.F01GrowthYoung

/-! The actual linear canonical growth and three-halves majorant growth
produce different explicit shifts. The constants precede epsilon. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

def canonicalGrowthShift (c K ε : ℝ) : ℝ := (1 + (c * K) ^ 2) * (1 + ε⁻¹)
def majorantGrowthShift (c K ε : ℝ) : ℝ :=
  (1 + c + c ^ 4 * K ^ 6) * (1 + (ε⁻¹) ^ 3)

theorem linear_quadratic_young {a u ε : ℝ} (hε : 0 < ε) :
    a * u - ε * u ^ 2 ≤ a ^ 2 / (4 * ε) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * ε)).mpr
  nlinarith [sq_nonneg (2 * ε * u - a)]

theorem canonicalGrowthShift_controls {c K ε r u w : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε)
    (hcompare : 1 + r ≤ K * u) (hgrowth : w ≤ c * (1 + r)) :
    w - ε * u ^ 2 - canonicalGrowthShift c K ε ≤ 0 := by
  have hlin : w ≤ (c * K) * u := by
    have hh := mul_le_mul_of_nonneg_left hcompare hc
    nlinarith
  have hy := linear_quadratic_young (a := c * K) (u := u) hε
  have hcoeff : (c * K) ^ 2 / 4 ≤ 1 + (c * K) ^ 2 := by
    nlinarith [sq_nonneg (c * K)]
  have hmul := mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hε.le)
  have hbound : (c * K) ^ 2 / (4 * ε) ≤ canonicalGrowthShift c K ε := by
    calc
      _ = ((c * K) ^ 2 / 4) * ε⁻¹ := by ring
      _ ≤ (1 + (c * K) ^ 2) * ε⁻¹ := hmul
      _ ≤ _ := by unfold canonicalGrowthShift; nlinarith [sq_nonneg (c * K)]
  linarith

theorem majorantGrowthShift_controls {c K ε r u w : ℝ}
    (hc : 0 ≤ c) (hK : 0 < K) (hε : 0 < ε) (hr : 0 ≤ r)
    (hcompare : 1 + r ≤ K * u) (hgrowth : w ≤ c * (1 + r ^ ((3 : ℝ) / 2))) :
    w - ε * u ^ 2 - majorantGrowthShift c K ε ≤ 0 := by
  have hru : r ≤ K * u := by linarith
  have hKu : 0 ≤ K * u := hr.trans hru
  have hsq : r ^ 2 ≤ (K * u) ^ 2 := (sq_le_sq₀ hr hKu).mpr hru
  have he3 : r ^ ((3 : ℝ) / 2) = (Real.sqrt r) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt 3 hr]
    norm_cast
  have he4 : (Real.sqrt r) ^ 4 = r ^ 2 := by
    calc
      _ = ((Real.sqrt r) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hr]
  have hdu : (ε / K ^ 2) * r ^ 2 ≤ ε * u ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hK)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hε.le]
  have hy := three_halves_shift_polynomial hc (div_pos hε (sq_pos_of_pos hK))
    (Real.sqrt_nonneg r)
  rw [he4] at hy
  rw [he3] at hgrowth
  have hright : c + c ^ 4 / (ε / K ^ 2) ^ 3 = c + (c ^ 4 * K ^ 6) * (ε⁻¹) ^ 3 := by
    field_simp
    <;> ring
  rw [hright] at hy
  have hshift : c + (c ^ 4 * K ^ 6) * (ε⁻¹) ^ 3 ≤ majorantGrowthShift c K ε := by
    unfold majorantGrowthShift
    nlinarith [pow_nonneg (inv_nonneg.mpr hε.le) 3,
      mul_nonneg hc (pow_nonneg (inv_nonneg.mpr hε.le) 3),
      mul_nonneg (pow_nonneg hc 4) (pow_nonneg hK.le 6)]
  linarith

end Yau.NodeProofs.F01Aux
