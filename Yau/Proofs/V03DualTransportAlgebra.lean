import Yau.Proofs.V03DualNorm

/-! Inverse-transpose covariance for the actual dual norm quadratic form.
The transformation is the transpose appropriate to covector coordinates. -/

open scoped Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem sesquilinear_congruence_quadratic (J : Matrix κ ι ℂ) (H : Matrix κ κ ℂ)
    (v : ι → ℂ) :
    star v ⬝ᵥ ((Jᴴ * H * J) *ᵥ v) =
      star (J *ᵥ v) ⬝ᵥ (H *ᵥ (J *ᵥ v)) := by
  conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.star_mulVec]

theorem inverse_transpose_congruence (H A : Matrix ι ι ℂ) (hA : IsUnit A) :
    Aᵀᴴ * ((Aᴴ * H * A)⁻¹)ᵀ * Aᵀ = (H⁻¹)ᵀ := by
  have hAdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hAH : IsUnit Aᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact hAdet.star
  have hAHdet := (Matrix.isUnit_iff_isUnit_det Aᴴ).mp hAH
  have hinv : (Aᴴ * H * A)⁻¹ = A⁻¹ * H⁻¹ * (Aᴴ)⁻¹ := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
  have hcancel : A * (Aᴴ * H * A)⁻¹ * Aᴴ = H⁻¹ := by
    rw [hinv]
    calc
      A * (A⁻¹ * H⁻¹ * (Aᴴ)⁻¹) * Aᴴ =
          (A * A⁻¹) * H⁻¹ * ((Aᴴ)⁻¹ * Aᴴ) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ := by
        rw [Matrix.mul_nonsing_inv A hAdet, Matrix.nonsing_inv_mul Aᴴ hAHdet,
          Matrix.one_mul, Matrix.mul_one]
  calc
    Aᵀᴴ * ((Aᴴ * H * A)⁻¹)ᵀ * Aᵀ = (A * (Aᴴ * H * A)⁻¹ * Aᴴ)ᵀ := by
      simp only [Matrix.transpose_mul,
        Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.mul_assoc]
    _ = (H⁻¹)ᵀ := congrArg Matrix.transpose hcancel

theorem dual_quadratic_congruence (H A : Matrix ι ι ℂ) (hA : IsUnit A) (v : ι → ℂ) :
    star (Aᵀ *ᵥ v) ⬝ᵥ (((Aᴴ * H * A)⁻¹)ᵀ *ᵥ (Aᵀ *ᵥ v)) =
      star v ⬝ᵥ ((H⁻¹)ᵀ *ᵥ v) := by
  rw [← sesquilinear_congruence_quadratic, inverse_transpose_congruence H A hA]

end Yau.Blueprint.V03Proof
