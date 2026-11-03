import Yau.Blueprint.Alignment

/-! The covector convention agrees with the actual conjugate Gram matrix. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem conjugate_quadratic (A B : Herm n) (v : Fin n → ℂ) :
    star (B *ᵥ v) ⬝ᵥ (A *ᵥ (B *ᵥ v)) =
      star v ⬝ᵥ ((B.conjTranspose * A * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc]

theorem inverse_transpose_conjugate (G P : Herm n) :
    ((P.conjTranspose * G * P)⁻¹).transpose =
      ((P⁻¹).transpose).conjTranspose * (G⁻¹).transpose * (P⁻¹).transpose := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.transpose_mul,
    ← Matrix.conjTranspose_nonsing_inv]
  simp only [Matrix.transpose_conjTranspose, Matrix.conjTranspose_transpose]

theorem dualNormMat_conjugate (G P : Herm n) (ξ : ComplexVector n) :
    dualNormMat (P.conjTranspose * G * P) ξ =
      dualNormMat G (WithLp.toLp 2 ((P⁻¹).transpose *ᵥ WithLp.ofLp ξ)) := by
  unfold dualNormMat
  rw [inverse_transpose_conjugate, conjugate_quadratic]

end Yau.Blueprint.Alignment.Y03Proof
