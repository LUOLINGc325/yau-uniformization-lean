import Yau.Proofs.E01Congruence

/-! Actual determinant maximality and feasibility are preserved by an invertible fiber change. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem determinant_congruence_re (S D : Herm n) :
    (Sᴴ * D * S).det.re = Complex.normSq S.det * D.det.re := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have heq : star S.det * D.det * S.det = (star S.det * S.det) * D.det := by ring
  rw [heq, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem matrixFiberMap_mul_inv (S : Herm n) (hS : IsUnit S) (η : ComplexVector n) :
    matrixFiberMap S (matrixFiberMap S⁻¹ η) = η := by
  rw [matrixFiberMap_comp, Matrix.mul_nonsing_inv _ (hS.map Matrix.detMonoidHom), matrixFiberMap_one]

theorem matrix_congruence_inverse_cancel (S D : Herm n) (hS : IsUnit S) :
    Sᴴ * (S⁻¹ᴴ * D * S⁻¹) * S = D := by
  have hRS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ (hS.map Matrix.detMonoidHom)
  calc
    Sᴴ * (S⁻¹ᴴ * D * S⁻¹) * S = (S⁻¹ * S)ᴴ * D * (S⁻¹ * S) := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = D := by rw [hRS]; simp

theorem normalized_minorant_max
    (v : ComplexVector n → EReal) (B S : Herm n) (hS : IsUnit S)
    (hSBS : Sᴴ * B * S = 1)
    (hmax : ∀ D : Herm n, D.PosDef →
      (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v η) → D.det.re ≤ B.det.re)
    (D : Herm n) (hD : D.PosDef)
    (hDv : ∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (matrixFiberMap S η)) :
    D.det.re ≤ 1 := by
  let A : Herm n := S⁻¹ᴴ * D * S⁻¹
  have hR : IsUnit S⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hS
  have hA : A.PosDef := hD.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr hR)
  have hAv : ∀ η, (ellipsoidQuadratic A η : EReal) ≤ v η := by
    intro η
    have h := hDv (matrixFiberMap S⁻¹ η)
    rw [matrixFiberMap_mul_inv S hS] at h
    simpa only [ellipsoidQuadratic_matrixFiberMap, A] using h
  have hb := mul_le_mul_of_nonneg_left (hmax A hA hAv) (Complex.normSq_nonneg S.det)
  rw [← determinant_congruence_re S A, ← determinant_congruence_re S B,
    hSBS, matrix_congruence_inverse_cancel S D hS] at hb
  simpa using hb

end Yau.NodeProofs.E01Aux
