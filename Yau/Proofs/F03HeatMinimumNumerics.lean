import Yau.Proofs.F03HeatTimeMajorants

/-! Exact scalar normalizations of the two actual heat estimates. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem le_common_constant_min {v q B C D : ℝ} (hq : 0 ≤ q)
    (hBD : B ≤ D) (hCD : C ≤ D) (hvB : v ≤ B) (hvC : v ≤ C*q) :
    v ≤ D*min 1 q := by
  by_cases hq1 : q ≤ 1
  · rw [min_eq_right hq1]
    exact hvC.trans (mul_le_mul_of_nonneg_right hCD hq)
  · rw [min_eq_left (lt_of_not_ge hq1).le,mul_one]
    exact hvB.trans hBD

theorem sqrt_scaled_le_of_fraction_bound {v C s L b q : ℝ} (hb : 0 < b)
    (hv : v ≤ C*s/(L*Real.sqrt b)*q) :
    v*Real.sqrt b ≤ C*(s/L)*q := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mp
  convert hv using 1 <;> ring

theorem div_sqrt_mul_le_of_scaled_bound {v C b q : ℝ} (hb : 0 < b)
    (hv : v*Real.sqrt b ≤ C*q) : v ≤ C/Real.sqrt b*q := by
  calc
    v ≤ (C*q)/Real.sqrt b := (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hv
    _ = _ := by ring

end Yau.Proofs.F03Aux
