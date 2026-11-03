import Yau.Proofs.Y02CoefficientBounds
import Yau.Proofs.Y02Homogeneous

/-! A fixed linear map on homogeneous coefficients has a uniform coefficient bound. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

def homogeneousExponents (n m : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finsupp.finite_of_degree_eq m).toFinset

theorem mem_homogeneousExponents (m : ℕ) (a : Fin n →₀ ℕ) :
    a ∈ homogeneousExponents n m ↔ a.degree = m := by
  simp [homogeneousExponents]

theorem norm_coeff_le_coeffNorm (P : PolyMap n) (i : Fin n) (a : Fin n →₀ ℕ) :
    ‖(P i).coeff a‖ ≤ P.coeffNorm := by
  classical
  by_cases ha : a ∈ (P i).support
  · apply (Finset.single_le_sum (fun b hb => norm_nonneg ((P i).coeff b)) ha).trans
    unfold PolyMap.coeffNorm
    exact Finset.single_le_sum (fun j hj => polynomialCoeffNorm_nonneg (P j)) (Finset.mem_univ i)
  · rw [notMem_support_iff.mp ha, norm_zero]
    exact coeffNorm_nonneg P

theorem homogeneous_scalar_expansion {m : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (hp : p.IsHomogeneous m) :
    p = ∑ a ∈ homogeneousExponents n m, p.coeff a • monomial a (1 : ℂ) := by
  classical
  rw [← support_sum_monomial_coeff p]
  have hsupport : p.support ⊆ homogeneousExponents n m := by
    intro a ha
    rw [mem_homogeneousExponents, Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp ha)
  calc
    _ = ∑ a ∈ homogeneousExponents n m, monomial a (p.coeff a) := by
      apply Finset.sum_subset hsupport
      intro a ha hnot
      simp [notMem_support_iff.mp hnot]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [smul_eq_C_mul, C_mul_monomial]

def homogeneousMonomialField (i : Fin n) (a : Fin n →₀ ℕ) : PolyMap n :=
  Pi.single i (monomial a 1)

theorem homogeneous_field_expansion {m : ℕ} (P : PolyMap n)
    (hP : P ∈ homogeneousFields n m) :
    P = ∑ i, ∑ a ∈ homogeneousExponents n m,
      (P i).coeff a • homogeneousMonomialField i a := by
  classical
  calc
    P = ∑ i, (Pi.single i (P i) : PolyMap n) :=
      (LinearMap.sum_single_apply (fun _ : Fin n => MvPolynomial (Fin n) ℂ) P).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      change (LinearMap.single ℂ (fun _ : Fin n => MvPolynomial (Fin n) ℂ) i) (P i) = _
      conv_lhs => rw [homogeneous_scalar_expansion (P i) (hP i)]
      simp only [map_sum, map_smul, LinearMap.single_apply, homogeneousMonomialField]

theorem exists_linear_coefficient_bound {ι : Type*} [Fintype ι]
    (m : ℕ) (R : PolyMap n →ₗ[ℂ] (ι → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : PolyMap n, P ∈ homogeneousFields n m →
      (∑ t, ‖R P t‖) ≤ C * P.coeffNorm := by
  classical
  let C : ℝ := ∑ t, ∑ i, ∑ a ∈ homogeneousExponents n m,
    ‖R (homogeneousMonomialField i a) t‖
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP
  have hexp : R P = ∑ i, ∑ a ∈ homogeneousExponents n m,
      (P i).coeff a • R (homogeneousMonomialField i a) := by
    conv_lhs => rw [homogeneous_field_expansion P hP]
    simp only [map_sum, map_smul]
  rw [hexp]
  calc
    _ ≤ ∑ t, ∑ i, ∑ a ∈ homogeneousExponents n m,
        ‖(P i).coeff a‖ * ‖R (homogeneousMonomialField i a) t‖ := by
      apply Finset.sum_le_sum
      intro t ht
      simp only [Finset.sum_apply, Pi.smul_apply]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      simp only [norm_smul]
      rfl
    _ ≤ ∑ t, ∑ i, ∑ a ∈ homogeneousExponents n m,
        P.coeffNorm * ‖R (homogeneousMonomialField i a) t‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (norm_coeff_le_coeffNorm P i a) (norm_nonneg _)
    _ = C * P.coeffNorm := by
      simp only [C, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      exact mul_comm _ _

end Yau.Proofs.Y02Aux
