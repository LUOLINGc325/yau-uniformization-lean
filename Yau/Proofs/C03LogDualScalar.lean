import Yau.Proofs.C03LogDualCauchy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact scalar inverse normalization and the real logarithmic bound. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C03Aux.LogDual

theorem real_scalar_identity_inverse_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℝ) (hd : 0 < d) :
    ((((d : ℂ) • (1 : Matrix ι ι ℂ))⁻¹)ᵀ) =
      ((d⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  letI : Invertible (d : ℂ) := invertibleOfNonzero hdn
  rw [Matrix.inv_smul (1 : Matrix ι ι ℂ) (d : ℂ) (by simp), inv_one,
    Matrix.transpose_smul, Matrix.transpose_one]
  simp only [invOf_eq_inv, Complex.ofReal_inv]

theorem log_le_uniform_bound (q A d : ℝ) (hq : 0 < q) (hA : 0 < A) (hd : 0 < d)
    (hbound : q ≤ A ^ 2 / d) :
    Real.log q ≤ max 0 (-Real.log d) + 2 * Real.log (1 + A) := by
  calc
    Real.log q ≤ Real.log (A ^ 2 / d) := Real.log_le_log hq hbound
    _ = 2 * Real.log A - Real.log d := by
      rw [Real.log_div (pow_ne_zero 2 hA.ne') hd.ne', Real.log_pow]
      norm_num
    _ ≤ max 0 (-Real.log d) + 2 * Real.log (1 + A) := by
      have hl := Real.log_le_log hA (show A ≤ 1 + A by linarith)
      have hdmax := le_max_right (0 : ℝ) (-Real.log d)
      linarith

end Yau.Proofs.C03Aux.LogDual
