import Yau.Proofs.Y02Linear
import Yau.Proofs.Y02QuantitativeStep

/-! Normalization by the exact inverse of the original linear matrix. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial Yau.Blueprint

variable {n : ℕ}

def normalizedJet (J : PolyMap n) : PolyMap n := (linearPoly J.linearPart⁻¹).comp J

theorem normalize_constantVolumeJet {d : ℕ} (J : PolyMap n) (hJ : IsConstantVolumeJet J d) :
    tangentId (normalizedJet J) ∧ IsConstantVolumeJet (normalizedJet J) d ∧
      (linearPoly J.linearPart).comp (normalizedJet J) = J ∧
      (normalizedJet J).coeffNorm ≤ ((n : ℝ) ^ 2 * matOpNorm J.linearPart⁻¹) * (1 + J.coeffNorm) := by
  classical
  have hunit : IsUnit J.linearPart.det := isUnit_iff_ne_zero.mpr hJ.2.2.1
  have hfix : (normalizedJet J).FixesZero := by
    intro i
    rw [normalizedJet, linearPoly_comp_apply, coeff_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [coeff_C_mul, hJ.1 j, mul_zero]
  have hlinear : (normalizedJet J).linearPart = 1 := by
    rw [normalizedJet, linearPoly_comp_linearPart, Matrix.nonsing_inv_mul J.linearPart hunit]
  have hdegree : (normalizedJet J).degree ≤ d := by
    apply (comp_degree_le (linearPoly J.linearPart⁻¹) J).trans
    apply le_trans (Nat.mul_le_mul_right J.degree (linearPoly_degree_le J.linearPart⁻¹))
    simpa only [one_mul] using hJ.2.1
  have hflat : positiveJacFlat (normalizedJet J) d := by
    intro a ha had
    rw [normalizedJet, linearPoly_comp_jacDet, coeff_C_mul, hJ.2.2.2 a ha had, mul_zero]
  have hconstant : IsConstantVolumeJet (normalizedJet J) d := by
    refine ⟨hfix, hdegree, ?_, hflat⟩
    rw [hlinear, Matrix.det_one]
    exact one_ne_zero
  refine ⟨⟨hfix, hlinear⟩, hconstant, ?_, ?_⟩
  · rw [normalizedJet, ← comp_assoc, (linearPoly_automorphism J.linearPart hJ.2.2.1).1, id_comp]
  · simpa only [pow_one, normalizedJet] using composition_bound_le (linearPoly J.linearPart⁻¹) J
      (linearPoly_degree_le _) (linearPoly_coeffNorm_le_matOpNorm _) (le_refl J.coeffNorm)

theorem normalizedJet_coeffNorm_le_square {d : ℕ} (J : PolyMap n) (hJ : IsConstantVolumeJet J d) :
    let S := 1 + J.coeffNorm + matOpNorm J.linearPart⁻¹
    1 ≤ S ∧ (normalizedJet J).coeffNorm ≤ (n : ℝ) ^ 2 * S ^ 2 ∧
      1 + (normalizedJet J).coeffNorm ≤ (1 + (n : ℝ) ^ 2) * S ^ 2 := by
  let S := 1 + J.coeffNorm + matOpNorm J.linearPart⁻¹
  have hinv : 0 ≤ matOpNorm J.linearPart⁻¹ := by unfold matOpNorm; exact norm_nonneg _
  have hS : 1 ≤ S := by dsimp [S]; linarith [coeffNorm_nonneg J]
  have hnorm := (normalize_constantVolumeJet J hJ).2.2.2
  have hbound : (normalizedJet J).coeffNorm ≤ (n : ℝ) ^ 2 * S ^ 2 := by
    apply hnorm.trans
    have hlin : matOpNorm J.linearPart⁻¹ ≤ S := by dsimp [S]; linarith [coeffNorm_nonneg J]
    have hjet : 1 + J.coeffNorm ≤ S := by dsimp [S]; linarith
    calc
      _ ≤ ((n : ℝ) ^ 2 * S) * S :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlin (sq_nonneg _)) hjet
          (by linarith [coeffNorm_nonneg J]) (by positivity)
      _ = _ := by ring
  refine ⟨hS, hbound, ?_⟩
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  nlinarith

end Yau.Proofs.Y02Aux
