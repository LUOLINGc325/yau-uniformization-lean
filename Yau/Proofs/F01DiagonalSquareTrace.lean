import spec.CHAIN.CONTRACTS

/-! Exact diagonal inverse and weighted squared first-jet trace identities
for the negative term in the actual log-determinant Hessian. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_real_diagonal (values : ι → ℝ) (hvalues : ∀ i, values i ≠ 0) :
    (Matrix.diagonal (fun i => (values i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i => (((values i)⁻¹ : ℝ) : ℂ)) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hvalues i), Complex.ofReal_one]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem weighted_square_trace (weights : ι → ℝ) (U : Matrix ι ι ℂ) :
    (Matrix.trace (Matrix.diagonal (fun i => (weights i : ℂ)) * Uᴴ *
      Matrix.diagonal (fun i => (weights i : ℂ)) * U)).re =
        ∑ i, ∑ j, weights i * weights j * Complex.normSq (U j i) := by
  have hentry (i : ι) : (Matrix.diagonal (fun i => (weights i : ℂ)) * Uᴴ *
      Matrix.diagonal (fun i => (weights i : ℂ)) * U) i i =
        ∑ j, ((weights i * weights j * Complex.normSq (U j i) : ℝ) : ℂ) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro j hj
    have hz : star (U j i) * U j i = (Complex.normSq (U j i) : ℂ) := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]
    calc
      (weights i : ℂ) * star (U j i) * (weights j : ℂ) * U j i =
          ((weights i * weights j : ℝ) : ℂ) * (star (U j i) * U j i) := by push_cast; ring
      _ = _ := by rw [hz, ← Complex.ofReal_mul]
  have hh : Matrix.trace (Matrix.diagonal (fun i => (weights i : ℂ)) * Uᴴ *
      Matrix.diagonal (fun i => (weights i : ℂ)) * U) =
        ∑ i, ∑ j, ((weights i * weights j * Complex.normSq (U j i) : ℝ) : ℂ) := by
    exact Finset.sum_congr rfl (fun i _ => hentry i)
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re hh

end Yau.NodeProofs.F01Aux
