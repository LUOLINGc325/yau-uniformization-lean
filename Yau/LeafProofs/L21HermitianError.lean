import Yau.LeafProofs.L21HermitianGram

/-! Finite quadratic-form errors are controlled by an actual uniform
entry bound and the exact squared Euclidean norm. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem finite_hermitian_error_norm_le {ι : Type*} [Fintype ι]
    (M : ι → ι → ℂ) (ξ : ι → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, ‖M i j‖ ≤ B) :
    ‖∑ i, ∑ j, star (ξ i) * M i j * ξ j‖ ≤
      (Fintype.card ι : ℝ) * B * ∑ i, ‖ξ i‖ ^ 2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
    (fun i => ‖ξ i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hCS
  have hprod : (∑ i, ∑ j, ‖ξ i‖ * B * ‖ξ j‖) = B * (∑ i, ‖ξ i‖) ^ 2 := by
    rw [← Finset.sum_mul_sum, ← Finset.sum_mul]
    ring
  calc
    _ ≤ ∑ i, ‖∑ j, star (ξ i) * M i j * ξ j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖ξ i‖ * B * ‖ξ j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)) (norm_nonneg _)
    _ = B * (∑ i, ‖ξ i‖) ^ 2 := hprod
    _ ≤ B * ((Fintype.card ι : ℝ) * ∑ i, ‖ξ i‖ ^ 2) := mul_le_mul_of_nonneg_left hCS hB
    _ = _ := by ring

theorem finite_hermitian_error_re_lower {ι : Type*} [Fintype ι]
    (M : ι → ι → ℂ) (ξ : ι → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ i j, ‖M i j‖ ≤ B) :
    -((Fintype.card ι : ℝ) * B * ∑ i, ‖ξ i‖ ^ 2) ≤
      (∑ i, ∑ j, star (ξ i) * M i j * ξ j).re := by
  have hh := (Complex.abs_re_le_norm _).trans (finite_hermitian_error_norm_le M ξ hB hM)
  exact (abs_le.mp hh).1

end Yau.LeafProofs.L21Aux
