import Yau.Proofs.P06SpectralClipVariation
import Yau.Proofs.P06MatrixHilbertSchmidt

noncomputable section
open scoped InnerProductSpace

namespace Yau.NodeProofs.P06Aux.Clip

theorem powerSlope_ofReal (a b : ℝ) (m : ℕ) :
    powerSlope (a : ℂ) (b : ℂ) m = ((powerSlope a b m : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m hm => simp only [powerSlope, hm, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]

theorem polynomialVariation_complex_diagonal_apply {n : ℕ} (p : Polynomial ℝ)
    (lam : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    polynomialVariation p (Matrix.diagonal (fun a => (lam a : ℂ))) D i j =
      D i j * ((polynomialSlope p (lam i) (lam j) : ℝ) : ℂ) := by
  classical
  simp only [polynomialVariation, Matrix.sum_apply, Matrix.smul_apply,
    powerVariation_diagonal_apply, powerSlope_ofReal, polynomialSlope,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem matrixToHS_norm_sq {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixToHS D‖ ^ 2 = ∑ i, ∑ j, ‖D i j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [matrixToHS, PiLp.toLp_apply, real_inner_self_eq_norm_sq, Fintype.sum_prod_type]

theorem polynomialVariation_complex_diagonal_energy_le {n : ℕ} (p : Polynomial ℝ)
    {R : ℝ} (lam : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hlam : ∀ i, lam i ∈ Set.Icc (-R) R)
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1) :
    ‖matrixToHS (polynomialVariation p (Matrix.diagonal (fun a => (lam a : ℂ))) D)‖ ^ 2 ≤
      ‖matrixToHS D‖ ^ 2 := by
  classical
  rw [matrixToHS_norm_sq, matrixToHS_norm_sq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [polynomialVariation_complex_diagonal_apply]
  have hs := polynomialSlope_abs_le_one p hder (hlam i) (hlam j)
  have hn : ‖D i j * ((polynomialSlope p (lam i) (lam j) : ℝ) : ℂ)‖ ≤ ‖D i j‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (mul_one _)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem polynomial_difference_sq_le (p : Polynomial ℝ) {R a b : ℝ}
    (hder : ∀ x ∈ Set.Icc (-R) R, |p.derivative.eval x| ≤ 1)
    (ha : a ∈ Set.Icc (-R) R) (hb : b ∈ Set.Icc (-R) R) :
    (p.eval a - p.eval b) ^ 2 ≤ (a - b) ^ 2 := by
  have hs := polynomialSlope_abs_le_one p hder ha hb
  have hn : |p.eval a - p.eval b| ≤ |a - b| := by
    rw [← polynomialSlope_mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans_eq (one_mul _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hn 2

end Yau.NodeProofs.P06Aux.Clip
