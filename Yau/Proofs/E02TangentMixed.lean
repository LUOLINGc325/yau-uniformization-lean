import Yau.Proofs.E02TangentDerivative

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem projectorTangent_adjoint_mul_self {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (projectorTangent M Z)ᴴ*projectorTangent M Z =
      (1-rowProjector M)*Zᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M) := by
  have hInv : (M*Mᴴ)⁻¹*(M*Mᴴ) = 1 :=
    Matrix.nonsing_inv_mul _ (hM.isUnit.map Matrix.detMonoidHom)
  rw [projectorTangent_conjTranspose M Z hM,projectorTangent]
  calc
    _ = (1-rowProjector M)*Zᴴ*((M*Mᴴ)⁻¹*(M*Mᴴ))*(M*Mᴴ)⁻¹*Z*(1-rowProjector M) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hInv]; simp

theorem projectorTangent_mul_adjoint_self {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    projectorTangent M Z*(projectorTangent M Z)ᴴ =
      Mᴴ*(M*Mᴴ)⁻¹*Z*(1-rowProjector M)*Zᴴ*(M*Mᴴ)⁻¹*M := by
  rw [projectorTangent_conjTranspose M Z hM,projectorTangent]
  calc
    _ = Mᴴ*(M*Mᴴ)⁻¹*Z*((1-rowProjector M)*(1-rowProjector M))*Zᴴ*(M*Mᴴ)⁻¹*M := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [one_sub_rowProjector_idempotent M hM]

/-- The barred combination of the two genuine real derivatives of S is
exactly SᴴS−SSᴴ, computed from the explicit Gram inverse and projector. -/
theorem projectorTangent_mixed_real_derivatives {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) :
    (1/2 : ℂ) • (fderiv ℝ (fun N => projectorTangent N Z) M Z+
      Complex.I • fderiv ℝ (fun N => projectorTangent N Z) M (Complex.I • Z)) =
      (projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ := by
  rw [projectorTangent_fderiv_apply_of_inverseGram M Z Z hM hInv,
    projectorTangent_fderiv_apply_of_inverseGram M Z (Complex.I • Z) hM hInv]
  simp only [projectorTangent_smul_direction,Matrix.conjTranspose_smul,
    Complex.star_def,Complex.conj_I]
  rw [projectorTangent_adjoint_mul_self M Z hM,projectorTangent_mul_adjoint_self M Z hM]
  simp only [projectorTangent_conjTranspose M Z hM]
  unfold projectorTangent rowProjector
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_I,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_neg,Matrix.neg_mul,
    smul_add,smul_sub,smul_smul,smul_neg,neg_smul,Matrix.mul_assoc,Complex.I_mul_I,Complex.I_sq]
  module

end Yau.NodeProofs.E02Aux
