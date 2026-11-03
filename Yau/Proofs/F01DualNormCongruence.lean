import Yau.LeafProofs.L17ChartNaturality

/-! Naturality of the native inverse-transpose cotangent norm under an
actual invertible complex change of frame. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem dualNormMat_congruence (G J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.det ≠ 0) (ξ : Fin n → ℂ) :
    dualNormMat (Jᴴ * G * J) (WithLp.toLp 2 (Jᵀ *ᵥ ξ)) =
      dualNormMat G (WithLp.toLp 2 ξ) := by
  have hleft : ((Jᴴ)⁻¹)ᵀ = ((J⁻¹)ᵀ)ᴴ := by
    rw [← Matrix.conjTranspose_nonsing_inv]
    exact (Matrix.conjTranspose_transpose_eq_transpose_conjTranspose _).symm
  have hmatrix : ((Jᴴ * G * J)⁻¹)ᵀ =
      ((J⁻¹)ᵀ)ᴴ * (G⁻¹)ᵀ * (J⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul,
      Matrix.transpose_mul, hleft]
  have hcancel : (J⁻¹)ᵀ *ᵥ (Jᵀ *ᵥ ξ) = ξ := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)]
    simp
  unfold dualNormMat
  simp only [WithLp.ofLp_toLp]
  rw [hmatrix, congruence_quadratic, hcancel]

end Yau.NodeProofs.F01Aux
