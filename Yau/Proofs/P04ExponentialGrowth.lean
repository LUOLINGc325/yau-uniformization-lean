import Yau.Proofs.P04GrowthAlgebra

noncomputable section

namespace Yau.Proofs.P04Aux

theorem polynomial_exp_le_linear_exp {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      A*Real.exp (a*(2+r))*(r+2)^m ≤ Real.exp (C*(1+r)) := by
  let C := |Real.log A|+2*a+(m : ℝ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun r hr => ?_⟩
  have hR : 0 < r+2 := by linarith
  have hlog : Real.log (r+2) ≤ 1+r := by
    have H := Real.log_le_sub_one_of_pos hR
    linarith
  have hfirst : Real.log A ≤ |Real.log A| * (1+r) := by
    have H := mul_nonneg (abs_nonneg (Real.log A)) hr
    nlinarith [le_abs_self (Real.log A)]
  have hsecond : a*(2+r) ≤ 2*a*(1+r) := by nlinarith [mul_nonneg ha hr]
  have hthird := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have heq : A*Real.exp (a*(2+r))*(r+2)^m =
      Real.exp (Real.log A+a*(2+r)+(m : ℝ)*Real.log (r+2)) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_log hA,Real.exp_nat_mul,Real.exp_log hR]
  rw [heq]
  apply Real.exp_le_exp.mpr
  dsimp only [C]
  nlinarith

end Yau.Proofs.P04Aux
