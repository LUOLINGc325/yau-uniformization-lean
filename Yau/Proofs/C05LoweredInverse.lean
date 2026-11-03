import Yau.Proofs.C05RicciDualEnergy
import Yau.LeafProofs.L23TensorEvaluation
import Yau.LeafProofs.L12JacobiCalculus
import Yau.LeafProofs.L23FieldMetricConnection

/-! Lower the actual inverse Ricci form with the real metric. These
matrix identities retain every metric and inverse derivative. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def loweredInverseMatrix (G A : Matrix ι ι ℝ) : Matrix ι ι ℝ := G * A⁻¹ * G

theorem loweredInverseMatrix_quadratic (G A : Matrix ι ι ℝ)
    (hG : G.IsSymm) (hdet : G.det ≠ 0) (p : ι → ℝ) :
    (G⁻¹ *ᵥ p) ⬝ᵥ (loweredInverseMatrix G A *ᵥ (G⁻¹ *ᵥ p)) =
      p ⬝ᵥ (A⁻¹ *ᵥ p) := by
  have hGp : G *ᵥ (G⁻¹ *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G
      (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  unfold loweredInverseMatrix
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGp,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG.eq, hGp]

theorem loweredInverseMatrix_time_algebra (G A B : Matrix ι ι ℝ)
    (hdet : A.det ≠ 0) :
    (-A) * A⁻¹ * G + G * (-(A⁻¹ * B * A⁻¹)) * G + G * A⁻¹ * (-A) =
      -(G + G) - G * A⁻¹ * B * A⁻¹ * G := by
  have hAI := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
  have hIA := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  have hl : (-A) * A⁻¹ * G = -G := by
    simp only [neg_mul, hAI, one_mul]
  have hr : G * A⁻¹ * (-A) = -G := by
    rw [mul_neg, mul_assoc G A⁻¹ A, hIA, mul_one]
  rw [hl, hr]
  noncomm_ring

theorem loweredInverseMatrix_covariant_algebra (G A D B : Matrix ι ι ℝ)
    (hdet : A.det ≠ 0) :
    (Dᵀ * G + G * D) * A⁻¹ * G +
      G * (-(A⁻¹ * (B + Dᵀ * A + A * D) * A⁻¹)) * G +
        G * A⁻¹ * (Dᵀ * G + G * D) -
          Dᵀ * loweredInverseMatrix G A - loweredInverseMatrix G A * D =
      -(G * A⁻¹ * B * A⁻¹ * G) := by
  have hAI := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)
  have hIA := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet)
  have hcancel₁ : A⁻¹ * (Dᵀ * A) * A⁻¹ = A⁻¹ * Dᵀ := by
    calc
      _ = A⁻¹ * (Dᵀ * (A * A⁻¹)) := by simp only [mul_assoc]
      _ = _ := by rw [hAI, mul_one]
  have hcancel₂ : A⁻¹ * (A * D) * A⁻¹ = D * A⁻¹ := by
    rw [← mul_assoc A⁻¹ A D, hIA, one_mul]
  simp only [mul_add, add_mul, mul_neg, neg_mul, hcancel₁, hcancel₂,
    loweredInverseMatrix]
  noncomm_ring

end Yau.Proofs.C05Aux
