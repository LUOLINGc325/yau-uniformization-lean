import Yau.Proofs.Y02CoefficientBounds

/-! Uniform degree and coefficient bounds under polynomial substitution. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

theorem polynomialCoeffNorm_prod {ι : Type*} (S : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (∏ i ∈ S, p i) ≤ ∏ i ∈ S, polynomialCoeffNorm (p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [polynomialCoeffNorm]
  | @insert i S hi hS =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (polynomialCoeffNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left hS (polynomialCoeffNorm_nonneg _))

theorem polynomialCoeffNorm_le_coeffNorm (P : PolyMap n) (i : Fin n) :
    polynomialCoeffNorm (P i) ≤ P.coeffNorm := by
  unfold PolyMap.coeffNorm
  exact Finset.single_le_sum (fun j hj => polynomialCoeffNorm_nonneg (P j))
    (Finset.mem_univ i)

theorem component_degree_le (P : PolyMap n) (i : Fin n) : (P i).totalDegree ≤ P.degree := by
  unfold PolyMap.degree
  exact Finset.le_sup (f := fun j : Fin n => (P j).totalDegree) (Finset.mem_univ i)

theorem polynomialCoeffNorm_bind_monomial (Q : PolyMap n) (a : Fin n →₀ ℕ) (c : ℂ) :
    polynomialCoeffNorm (bind₁ Q (monomial a c)) ≤
      ‖c‖ * (1 + Q.coeffNorm) ^ a.degree := by
  classical
  rw [bind₁_monomial, polynomialCoeffNorm_C_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  apply (polynomialCoeffNorm_prod _ _).trans
  calc
    _ ≤ ∏ j ∈ a.support, (1 + Q.coeffNorm) ^ a j := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact polynomialCoeffNorm_nonneg _
      · intro j hj
        apply (polynomialCoeffNorm_pow _ _).trans
        apply pow_le_pow_left₀ (polynomialCoeffNorm_nonneg _)
        exact (polynomialCoeffNorm_le_coeffNorm Q j).trans (by linarith)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]; rfl

theorem polynomialCoeffNorm_bind (Q : PolyMap n) (p : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (bind₁ Q p) ≤ polynomialCoeffNorm p * (1 + Q.coeffNorm) ^ p.totalDegree := by
  classical
  have hexp : bind₁ Q p = ∑ a ∈ p.support, bind₁ Q (monomial a (p.coeff a)) := by
    rw [← map_sum]
    rw [support_sum_monomial_coeff]
  rw [hexp]
  apply (polynomialCoeffNorm_sum _ _).trans
  calc
    _ ≤ ∑ a ∈ p.support, ‖p.coeff a‖ * (1 + Q.coeffNorm) ^ p.totalDegree := by
      apply Finset.sum_le_sum
      intro a ha
      apply (polynomialCoeffNorm_bind_monomial Q a _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply pow_le_pow_right₀ (by linarith [coeffNorm_nonneg Q])
      exact le_totalDegree ha
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem comp_coeffNorm_le (P Q : PolyMap n) :
    (P.comp Q).coeffNorm ≤ P.coeffNorm * (1 + Q.coeffNorm) ^ P.degree := by
  classical
  change (∑ i, polynomialCoeffNorm (bind₁ Q (P i))) ≤ _
  calc
    _ ≤ ∑ i, polynomialCoeffNorm (P i) * (1 + Q.coeffNorm) ^ P.degree := by
      apply Finset.sum_le_sum
      intro i hi
      apply (polynomialCoeffNorm_bind Q (P i)).trans
      apply mul_le_mul_of_nonneg_left _ (polynomialCoeffNorm_nonneg _)
      apply pow_le_pow_right₀ (by linarith [coeffNorm_nonneg Q])
      exact component_degree_le P i
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem totalDegree_bind_monomial_le (Q : PolyMap n) (a : Fin n →₀ ℕ) (c : ℂ) :
    (bind₁ Q (monomial a c)).totalDegree ≤ a.degree * Q.degree := by
  classical
  rw [bind₁_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ j ∈ a.support, a j * Q.degree := by
      apply Finset.sum_le_sum
      intro j hj
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (component_degree_le Q j))
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem totalDegree_bind_le (Q : PolyMap n) (p : MvPolynomial (Fin n) ℂ) :
    (bind₁ Q p).totalDegree ≤ p.totalDegree * Q.degree := by
  classical
  have hexp : bind₁ Q p = ∑ a ∈ p.support, bind₁ Q (monomial a (p.coeff a)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [hexp]
  apply totalDegree_finsetSum_le
  intro a ha
  exact (totalDegree_bind_monomial_le Q a _).trans
    (Nat.mul_le_mul_right _ (le_totalDegree ha))

theorem comp_degree_le (P Q : PolyMap n) : (P.comp Q).degree ≤ P.degree * Q.degree := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  exact (totalDegree_bind_le Q (P i)).trans
    (Nat.mul_le_mul_right _ (component_degree_le P i))

end Yau.Proofs.Y02Aux
