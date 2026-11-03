import Yau.Proofs.Y06Homogeneous
import Yau.Proofs.Y06ProjectionNorm

/-! The complete linear jump conjugation has an operator bound proportional
to the incoming coefficient norm, including when that norm is zero. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem linear_comp_coeffNorm_bound (A : Herm n) (P : PolyMap n) :
    ((linearPolynomial A).comp P).coeffNorm ≤
      (∑ i, ∑ j, ‖A i j‖) * P.coeffNorm := by
  classical
  change (∑ i, polynomialCoeffNorm ((linearPoly A).comp P i)) ≤ _
  calc
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * polynomialCoeffNorm (P j) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [linearPoly_comp_apply]
      apply (polynomialCoeffNorm_sum _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_eq (polynomialCoeffNorm_C_mul (A i j) (P j))
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * P.coeffNorm := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (polynomialCoeffNorm_le_coeffNorm P j) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_mul]

theorem homogeneous_comp_coeffNorm_bound {P : PolyMap n} (hP : Homogeneous P m) (Q : PolyMap n) :
    (P.comp Q).coeffNorm ≤ P.coeffNorm * (1 + Q.coeffNorm) ^ m := by
  apply (comp_coeffNorm_le P Q).trans
  apply mul_le_mul_of_nonneg_left _ (coeffNorm_nonneg P)
  exact pow_le_pow_right₀ (by linarith [coeffNorm_nonneg Q]) (homogeneous_degree_le hP)

theorem linear_conjugation_coeffNorm_bound (J : Herm n) {P : PolyMap n}
    (hP : Homogeneous P m) :
    (((linearPolynomial J⁻¹).comp (P.comp (linearPolynomial J)))).coeffNorm ≤
      ((∑ i, ∑ j, ‖J⁻¹ i j‖) * (1 + (linearPolynomial J).coeffNorm) ^ m) * P.coeffNorm := by
  have hleft := linear_comp_coeffNorm_bound J⁻¹ (P.comp (linearPolynomial J))
  have hright := homogeneous_comp_coeffNorm_bound hP (linearPolynomial J)
  have hmul := mul_le_mul_of_nonneg_left hright
    (by positivity : 0 ≤ ∑ i, ∑ j, ‖J⁻¹ i j‖)
  exact hleft.trans (hmul.trans_eq (by ring))

theorem backwardOperator_coeffNorm_bound (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (J : Herm n) (w : Fin n → ℝ) {P : PolyMap n} (hP : Homogeneous P m)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hfactor : ∀ i (β : Fin n →₀ ℕ), β.sum (fun _ e => e) = m →
      w i < ∑ l, (β l : ℝ) * w l →
        ‖(a i)⁻¹‖ * (∏ l ∈ β.support, ‖a l‖ ^ β l) ≤ δ) :
    (backwardOperator (Matrix.diagonal a) J w P).coeffNorm ≤
      (δ * (∑ i, ∑ j, ‖J⁻¹ i j‖) * (1 + (linearPolynomial J).coeffNorm) ^ m) * P.coeffNorm := by
  classical
  let Y := (linearPolynomial J⁻¹).comp (P.comp (linearPolynomial J))
  have hY : Homogeneous Y m := homogeneous_linear_comp (homogeneous_comp_linear hP J) J⁻¹
  have hbound : (backwardOperator (Matrix.diagonal a) J w P).coeffNorm ≤ δ * Y.coeffNorm := by
    apply coeffNorm_le_of_coeff_bound
    intro i β
    rw [backwardOperator_diagonal_coeff a ha]
    by_cases hf : w i < ∑ l, (β l : ℝ) * w l
    · rw [ite_eq_left hf]
      change ‖((a i)⁻¹ * ∏ l ∈ β.support, a l ^ β l) * (Y i).coeff β‖ ≤ _
      simp only [norm_mul, norm_prod, norm_pow]
      by_cases hz : (Y i).coeff β = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (hfactor i β (hY i β hz) hf) (norm_nonneg _)
    · rw [ite_eq_right hf, norm_zero]
      exact mul_nonneg hδ (norm_nonneg _)
  have hconj := linear_conjugation_coeffNorm_bound J hP
  have hmul := mul_le_mul_of_nonneg_left hconj hδ
  exact hbound.trans (hmul.trans_eq (by ring))

end Yau.Proofs.Y06Aux
