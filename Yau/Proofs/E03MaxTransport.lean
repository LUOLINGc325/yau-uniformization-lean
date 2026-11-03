import Yau.Proofs.E01NormalizeMax

/-! SOURCE-ONLY E03 candidate: general invertible transport, reusing canonical congruence algebra. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint
open Yau.NodeProofs.E01Aux

variable {n : ℕ}

theorem determinant_maximum_congruence
    (v : ComplexVector n → EReal) (B S : Herm n) (hB : B.PosDef) (hS : IsUnit S)
    (hBv : ∀ η, (ellipsoidQuadratic B η : EReal) ≤ v η)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re) :
    (Sᴴ * B * S).PosDef ∧
      (∀ η, (ellipsoidQuadratic (Sᴴ * B * S) η : EReal) ≤ v (matrixFiberMap S η)) ∧
      ∀ D : Herm n, D.PosDef →
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (matrixFiberMap S η)) →
        D.det.re ≤ (Sᴴ * B * S).det.re := by
  refine ⟨hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hS), ?_, ?_⟩
  · intro η
    simpa only [ellipsoidQuadratic_matrixFiberMap] using hBv (matrixFiberMap S η)
  · intro D hD hDv
    let A : Herm n := S⁻¹ᴴ * D * S⁻¹
    have hR : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hS
    have hA : A.PosDef := hD.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hR)
    have hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η := by
      intro η
      have h := hDv (matrixFiberMap S⁻¹ η)
      rw [matrixFiberMap_mul_inv S hS] at h
      simpa only [ellipsoidQuadratic_matrixFiberMap, A] using h
    have hc := mul_le_mul_of_nonneg_left (hmax A hA hAv) (Complex.normSq_nonneg S.det)
    rw [← determinant_congruence_re S A, ← determinant_congruence_re S B,
      matrix_congruence_inverse_cancel S D hS] at hc
    exact hc

end Yau.NodeProofs.E03Aux
