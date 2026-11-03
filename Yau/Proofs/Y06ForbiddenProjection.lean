import Yau.Proofs.Y01PolynomialComposition
import spec.CHAIN.CONTRACTS

/-! The original forbidden projection is a coordinate projection in the
coefficient norm. Its input has no support restriction. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem forbiddenProjection_coeff (w : Fin n → ℝ) (X : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) :
    (forbiddenProjection w X i).coeff β =
      if w i < ∑ l, (β l : ℝ) * w l then (X i).coeff β else 0 := by
  classical
  have hterm (γ : Fin n →₀ ℕ) :
      (if w i < ∑ l, (γ l : ℝ) * w l then monomial γ ((X i).coeff γ) else 0).coeff β =
        if γ = β then (if w i < ∑ l, (β l : ℝ) * w l then (X i).coeff β else 0) else 0 := by
    by_cases hγ : γ = β
    · subst γ
      by_cases hf : w i < ∑ l, (β l : ℝ) * w l <;> simp [hf]
    · by_cases hf : w i < ∑ l, (γ l : ℝ) * w l <;> simp [hf, coeff_monomial, hγ]
  unfold forbiddenProjection
  rw [coeff_sum]
  simp_rw [hterm]
  by_cases hβ : β ∈ (X i).support
  · simp [hβ]
  · have hz : (X i).coeff β = 0 := notMem_support_iff.mp hβ
    simp [hz]

theorem forbiddenProjection_support (w : Fin n → ℝ) (X : PolyMap n) (i : Fin n) :
    (forbiddenProjection w X i).support ⊆ (X i).support := by
  classical
  intro β hβ
  rw [mem_support_iff, forbiddenProjection_coeff] at hβ
  apply mem_support_iff.mpr
  split_ifs at hβ
  · exact hβ
  · exact False.elim (hβ rfl)

theorem coeffNorm_le_of_coeff_bound {P Q : PolyMap n} {a : ℝ}
    (h : ∀ i β, ‖(P i).coeff β‖ ≤ a * ‖(Q i).coeff β‖) :
    P.coeffNorm ≤ a * Q.coeffNorm := by
  classical
  have hsupport i : (P i).support ⊆ (Q i).support := by
    intro β hβ
    apply mem_support_iff.mpr
    intro hz
    have hle := h i β
    rw [hz, norm_zero, mul_zero] at hle
    have hzero : (P i).coeff β = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    exact mem_support_iff.mp hβ hzero
  unfold PolyMap.coeffNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  change polynomialCoeffNorm (P i) ≤ a * polynomialCoeffNorm (Q i)
  rw [← sum_norm_coeff_eq (P i) (Q i).support (hsupport i)]
  change (∑ β ∈ (Q i).support, ‖(P i).coeff β‖) ≤
    a * ∑ β ∈ (Q i).support, ‖(Q i).coeff β‖
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun β hβ => h i β)

theorem forbiddenProjection_coeffNorm (w : Fin n → ℝ) (X : PolyMap n) :
    (forbiddenProjection w X).coeffNorm ≤ X.coeffNorm := by
  have h : (forbiddenProjection w X).coeffNorm ≤ 1 * X.coeffNorm := by
    apply coeffNorm_le_of_coeff_bound
    intro i β
    rw [forbiddenProjection_coeff]
    split_ifs
    · simp
    · simp
  simpa only [one_mul] using h

theorem forbiddenProjection_homogeneous (w : Fin n → ℝ) {X : PolyMap n} {m : ℕ}
    (hX : Homogeneous X m) : Homogeneous (forbiddenProjection w X) m := by
  intro i β hβ
  rw [forbiddenProjection_coeff] at hβ
  split_ifs at hβ
  · exact hX i β hβ
  · exact False.elim (hβ rfl)

theorem forbiddenProjection_forbidden (w : Fin n → ℝ) (X : PolyMap n)
    (i : Fin n) (β : Fin n →₀ ℕ) (hβ : (forbiddenProjection w X i).coeff β ≠ 0) :
    w i < ∑ l, (β l : ℝ) * w l := by
  rw [forbiddenProjection_coeff] at hβ
  by_contra hnot
  exact hβ (ite_eq_right hnot)

theorem forbiddenProjection_idempotent (w : Fin n → ℝ) (X : PolyMap n) :
    forbiddenProjection w (forbiddenProjection w X) = forbiddenProjection w X := by
  funext i
  ext β
  simp only [forbiddenProjection_coeff]
  split_ifs <;> rfl

end Yau.Proofs.Y06Aux
