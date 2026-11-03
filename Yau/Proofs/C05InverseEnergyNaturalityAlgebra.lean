import Yau.Proofs.C05LoweredInverse

/-! Inverse energy and its lowered inverse tensor are invariant under
an arbitrary invertible real change of frame. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C05Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverseMatrix_congruence (J A : Matrix ι ι ℝ) (hJ : J.det ≠ 0) :
    J * (Jᵀ * A * J)⁻¹ * Jᵀ = A⁻¹ := by
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hJTu := Matrix.isUnit_det_transpose J hJu
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  change J * (J⁻¹ * (A⁻¹ * Jᵀ⁻¹)) * Jᵀ = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJu,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJTu, Matrix.mul_one]

theorem inverseMatrixEnergy_congruence (J A : Matrix ι ι ℝ) (hJ : J.det ≠ 0)
    (p : ι → ℝ) :
    (Jᵀ *ᵥ p) ⬝ᵥ ((Jᵀ * A * J)⁻¹ *ᵥ (Jᵀ *ᵥ p)) = p ⬝ᵥ (A⁻¹ *ᵥ p) := by
  have hpair (w : ι → ℝ) : (Jᵀ *ᵥ p) ⬝ᵥ w = p ⬝ᵥ (J *ᵥ w) := by
    rw [dotProduct_comm]
    exact Matrix.dotProduct_transpose_mulVec J w p
  rw [hpair, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, inverseMatrix_congruence J A hJ]

theorem loweredInverseMatrix_congruence (J G A : Matrix ι ι ℝ) (hJ : J.det ≠ 0) :
    loweredInverseMatrix (Jᵀ * G * J) (Jᵀ * A * J) =
      Jᵀ * loweredInverseMatrix G A * J := by
  calc
    _ = Jᵀ * G * (J * (Jᵀ * A * J)⁻¹ * Jᵀ) * G * J := by
      unfold loweredInverseMatrix
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [inverseMatrix_congruence J A hJ]
      simp only [loweredInverseMatrix, Matrix.mul_assoc]

end Yau.Proofs.C05Aux
