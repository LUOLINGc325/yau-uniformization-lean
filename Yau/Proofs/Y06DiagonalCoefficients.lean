import Yau.Proofs.Y06ForbiddenProjection

/-! Expand the entire jump conjugation before extracting the diagonal
factor of each forbidden coefficient. The incoming polynomial is arbitrary. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n : ℕ}

theorem linearPolynomial_diagonal_apply (a : Fin n → ℂ) (i : Fin n) :
    linearPolynomial (Matrix.diagonal a) i = C (a i) * X i := by
  classical
  simp [linearPolynomial, Matrix.diagonal_apply, apply_ite]

theorem diagonal_bind_monomial (a : Fin n → ℂ) (β : Fin n →₀ ℕ) (c : ℂ) :
    bind₁ (fun j => C (a j) * X j) (monomial β c) =
      monomial β (c * ∏ j ∈ β.support, a j ^ β j) := by
  classical
  rw [bind₁_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [← mul_assoc, ← map_mul, prod_X_pow_eq_monomial, C_mul_monomial, mul_one]

theorem diagonal_bind_coeff (a : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ)
    (β : Fin n →₀ ℕ) :
    (bind₁ (fun j => C (a j) * X j) p).coeff β =
      (∏ j ∈ β.support, a j ^ β j) * p.coeff β := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial γ c =>
    rw [diagonal_bind_monomial]
    by_cases hγ : γ = β
    · subst γ
      simp only [coeff_monomial, ite_true]
      ring
    · simp [coeff_monomial, hγ]
  | add p q hp hq =>
    rw [map_add]
    change ((bind₁ (fun j => C (a j) * X j)) p).coeff β +
      ((bind₁ (fun j => C (a j) * X j)) q).coeff β =
        (∏ j ∈ β.support, a j ^ β j) * (p.coeff β + q.coeff β)
    rw [hp, hq, mul_add]

theorem diagonal_sandwich_coeff (a b : Fin n → ℂ) (P : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    ((linearPolynomial (Matrix.diagonal a)).comp
      (P.comp (linearPolynomial (Matrix.diagonal b))) i).coeff β =
      (a i * ∏ j ∈ β.support, b j ^ β j) * (P i).coeff β := by
  classical
  have hleft (Q : PolyMap n) :
      (linearPolynomial (Matrix.diagonal a)).comp Q i = C (a i) * Q i := by
    change (linearPoly (Matrix.diagonal a)).comp Q i = _
    rw [linearPoly_comp_apply]
    simp [Matrix.diagonal_apply, apply_ite]
  have hright : linearPolynomial (Matrix.diagonal b) = (fun j => C (b j) * X j) :=
    funext (linearPolynomial_diagonal_apply b)
  rw [hleft, coeff_C_mul, hright]
  change a i * (bind₁ (fun j => C (b j) * X j) (P i)).coeff β = _
  rw [diagonal_bind_coeff]
  ring

theorem diagonal_sandwich_norm_coeff (a b : Fin n → ℂ) (P : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    ‖((linearPolynomial (Matrix.diagonal a)).comp
      (P.comp (linearPolynomial (Matrix.diagonal b))) i).coeff β‖ =
      (‖a i‖ * ∏ j ∈ β.support, ‖b j‖ ^ β j) * ‖(P i).coeff β‖ := by
  rw [diagonal_sandwich_coeff]
  simp only [norm_mul, norm_prod, norm_pow]

theorem backwardOperator_diagonal_coeff (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (J : Herm n) (w : Fin n → ℝ) (P : PolyMap n) (i : Fin n) (β : Fin n →₀ ℕ) :
    (backwardOperator (Matrix.diagonal a) J w P i).coeff β =
      if w i < ∑ l, (β l : ℝ) * w l then
        ((a i)⁻¹ * ∏ j ∈ β.support, a j ^ β j) *
          (((linearPolynomial J⁻¹).comp (P.comp (linearPolynomial J))) i).coeff β
      else 0 := by
  classical
  have hinv : (Matrix.diagonal a)⁻¹ = Matrix.diagonal (fun i => (a i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (ha j)
  have hcomp : linearPolynomial (J * Matrix.diagonal a) =
      (linearPolynomial J).comp (linearPolynomial (Matrix.diagonal a)) :=
    (linearPoly_comp J (Matrix.diagonal a)).symm
  unfold backwardOperator
  rw [forbiddenProjection_coeff, hinv, hcomp]
  have heq : (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).comp
      ((linearPolynomial J⁻¹).comp (P.comp ((linearPolynomial J).comp (linearPolynomial (Matrix.diagonal a))))) =
      (linearPolynomial (Matrix.diagonal (fun i => (a i)⁻¹))).comp
        (((linearPolynomial J⁻¹).comp (P.comp (linearPolynomial J))).comp
          (linearPolynomial (Matrix.diagonal a))) := by
    simp only [comp_assoc]
  rw [heq, diagonal_sandwich_coeff]

end Yau.Proofs.Y06Aux
