import Yau.Proofs.Y02JacobianComposition
import Yau.Proofs.Y05FiniteJets

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment MvPolynomial Yau.Proofs.Y02Aux
open scoped BigOperators

variable {n : ℕ}

theorem pderiv_integrateLast (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    pderiv last (integrateLast last E) = E := by
  classical
  unfold integrateLast
  rw [map_sum]
  conv_rhs => rw [← support_sum_monomial_coeff E]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pderiv_monomial, add_tsub_cancel_right]
  congr 1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
  exact div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero (a last))

theorem integrateLast_degree (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (integrateLast last E).totalDegree ≤ E.totalDegree + 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro a ha
  apply (totalDegree_monomial_le _ _).trans
  change (a + Finsupp.single last 1).degree ≤ E.totalDegree + 1
  have H : a.degree ≤ E.totalDegree := le_totalDegree ha
  simpa only [map_add, Finsupp.degree_single] using Nat.add_le_add_right H 1

theorem integrateLast_zero (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (integrateLast last E).coeff 0 = 0 := by
  classical
  unfold integrateLast
  rw [coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [coeff_monomial]
  apply if_neg
  intro he
  have H := congrArg (fun b : Fin n →₀ ℕ => b last) he
  simp at H

theorem integrateLast_linear_coefficient (last j : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (integrateLast last E).coeff (Finsupp.single j 1) = if j = last then E.coeff 0 else 0 := by
  classical
  by_cases hj : j = last
  · subst j
    rw [if_pos rfl]
    have H := congrArg (fun P : MvPolynomial (Fin n) ℂ => P.coeff 0)
      (pderiv_integrateLast last E)
    simpa [coeff_pderiv] using H
  · rw [if_neg hj]
    unfold integrateLast
    rw [coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    rw [coeff_monomial]
    apply if_neg
    intro he
    have H := congrArg (fun a : Fin n →₀ ℕ => a last) he
    simp [Finsupp.single_apply, hj, Ne.symm hj] at H

theorem integrateLast_coeffNorm (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    polynomialCoeffNorm (integrateLast last E) ≤ polynomialCoeffNorm E := by
  apply (polynomialCoeffNorm_sum _ _).trans
  unfold polynomialCoeffNorm
  apply Finset.sum_le_sum
  intro a ha
  change polynomialCoeffNorm (monomial (a + Finsupp.single last 1)
    (E.coeff a / (a last + 1 : ℂ))) ≤ ‖E.coeff a‖
  rw [polynomialCoeffNorm_monomial, norm_div]
  apply div_le_self (norm_nonneg _)
  norm_cast
  omega

theorem volumeMap_fixesZero (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (volumeMap last E).FixesZero := by
  intro i
  by_cases hi : i = last
  · subst i; simpa [volumeMap] using integrateLast_zero last E
  · simp [volumeMap, hi, coeff_X]

theorem volumeMap_linearPart (last : Fin n) (E : MvPolynomial (Fin n) ℂ)
    (hE : E.coeff 0 = 1) : (volumeMap last E).linearPart = 1 := by
  ext i j
  by_cases hi : i = last
  · subst i
    simp [PolyMap.linearPart, volumeMap, integrateLast_linear_coefficient, hE,
      Matrix.one_apply, eq_comm]
  · simp [PolyMap.linearPart, volumeMap, hi, coeff_X, Matrix.one_apply, eq_comm,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

theorem volumeMap_degree (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (volumeMap last E).degree ≤ E.totalDegree + 1 := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  by_cases hil : i = last
  · subst i; simpa [volumeMap] using integrateLast_degree last E
  · simp only [volumeMap, if_neg hil, totalDegree_X]
    omega

theorem volumeMap_coeffNorm (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (volumeMap last E).coeffNorm ≤ (n : ℝ) * (1 + polynomialCoeffNorm E) := by
  classical
  change (∑ i, polynomialCoeffNorm (volumeMap last E i)) ≤ _
  calc
    _ ≤ ∑ _i : Fin n, (1 + polynomialCoeffNorm E) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hil : i = last
      · subst i
        simp only [volumeMap, ite_true]
        have H := integrateLast_coeffNorm last E
        linarith
      · simp only [volumeMap, if_neg hil]
        have hX : polynomialCoeffNorm (X i : MvPolynomial (Fin n) ℂ) = 1 := by
          simp [X, polynomialCoeffNorm_monomial]
        rw [hX]
        linarith [polynomialCoeffNorm_nonneg E]
    _ = _ := by simp; ring

theorem jacDet_volumeMap (last : Fin n) (E : MvPolynomial (Fin n) ℂ) :
    (volumeMap last E).jacDet = E := by
  classical
  let v : Fin n → MvPolynomial (Fin n) ℂ := fun j => pderiv j (integrateLast last E)
  have hmat : Yau.Proofs.Y02Aux.jacobianMatrix (volumeMap last E) =
      (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℂ)).updateRow last v := by
    apply Matrix.ext
    intro i j
    by_cases hi : i = last
    · subst i; simp [Yau.Proofs.Y02Aux.jacobianMatrix, volumeMap, Matrix.updateRow,
        Function.update, v]
    · simp [Yau.Proofs.Y02Aux.jacobianMatrix, volumeMap, hi, Matrix.updateRow,
        Function.update, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  have hv : v = ∑ j : Fin n, v j •
      (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℂ)) j := by
    ext i
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  change (Yau.Proofs.Y02Aux.jacobianMatrix (volumeMap last E)).det = E
  rw [hmat, hv, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
  exact pderiv_integrateLast last E

end Yau.Proofs.Y05Aux
