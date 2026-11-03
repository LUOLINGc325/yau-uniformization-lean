import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Elementary exact numerical bounds in the final comparison-weight estimates. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem weight_gradient_square_bound {a b r v : ℝ} (hr : 0 < r) (hv : 1 ≤ v) :
    ((a+b/v)/r)^2 ≤ (2*a^2+2*b^2/v)/r^2 := by
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have hBasic : (a*v+b)^2 ≤ 2*a^2*v^2+2*b^2*v := by
    nlinarith [sq_nonneg (a*v-b),mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hv)]
  have hDiv := div_le_div_of_nonneg_right hBasic (sq_nonneg v)
  have hNumerator : (a+b/v)^2 ≤ 2*a^2+2*b^2/v := by
    convert hDiv using 1 <;> field_simp <;> ring
  rw [div_pow]
  exact div_le_div_of_nonneg_right hNumerator (sq_nonneg r)

end Yau.Proofs.F03Aux
