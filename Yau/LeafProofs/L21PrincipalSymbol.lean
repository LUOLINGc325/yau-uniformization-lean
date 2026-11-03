import Yau.LeafProofs.L21OperatorRows

/-! Orthogonality of the ordinary holomorphic and antiholomorphic real
rows. This preserves the positive radial Hessian term in the boundary
weight, without an estimate by the Hessian operator norm. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def rowCombination (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (ξ : Fin n → ℂ) (a : Yau.RIdx n) : ℂ :=
  ∑ i, ξ i * dbarRealCoefficient A i a x

theorem rowCombination_real (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (ξ : Fin n → ℂ) (k : Fin n) :
    rowCombination A x ξ (k, 0) = (1 / 2 : ℂ) * (ξ k + ∑ i, ξ i * A x i k) := by
  classical
  simp only [rowCombination, dbarRealCoefficient, wirtBarRealCoefficient,
    wirtRealCoefficient, ite_true, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  ring

theorem rowCombination_imag (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (ξ : Fin n → ℂ) (k : Fin n) :
    rowCombination A x ξ (k, 1) = (Complex.I / 2 : ℂ) * (ξ k - ∑ i, ξ i * A x i k) := by
  classical
  simp only [rowCombination, dbarRealCoefficient, wirtBarRealCoefficient,
    wirtRealCoefficient, mul_add, Finset.sum_add_distrib,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  norm_num
  rw [mul_sub, Finset.mul_sum]
  have hs : (∑ i, ξ i * (A x i k * (-Complex.I / 2))) =
      -(∑ i, Complex.I / 2 * (ξ i * A x i k)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem complex_half_parallelogram (u v : ℂ) :
    ‖(1 / 2 : ℂ) * (u + v)‖ ^ 2 + ‖(Complex.I / 2 : ℂ) * (u - v)‖ ^ 2 =
      (1 / 2 : ℝ) * ‖u‖ ^ 2 + (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, Complex.norm_I, mul_pow]
  norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem principal_symbol_norm_sq (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (ξ : Fin n → ℂ) :
    (∑ a : Yau.RIdx n, ‖rowCombination A x ξ a‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ i, ‖ξ i‖ ^ 2 +
        (1 / 2 : ℝ) * ∑ k, ‖∑ i, ξ i * A x i k‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, rowCombination_real, rowCombination_imag,
    complex_half_parallelogram, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem principal_symbol_lower_bound (A : X n → Matrix (Fin n) (Fin n) ℂ)
    (x : X n) (ξ : Fin n → ℂ) :
    (1 / 2 : ℝ) * ∑ i, ‖ξ i‖ ^ 2 ≤ ∑ a : Yau.RIdx n, ‖rowCombination A x ξ a‖ ^ 2 := by
  rw [principal_symbol_norm_sq]
  exact le_add_of_nonneg_right (by positivity)

end Yau.LeafProofs.L21Aux
