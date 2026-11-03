import Yau.Proofs.E02ProjectorFirst

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem projectorTangent_differentiableAt_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) :
    DifferentiableAt ℝ (fun N => projectorTangent N Z) M := by
  have hLeft := (rectMulCLM m n n).hasFDerivAt_of_bilinear
    (rectAdjointCLM n m).hasFDerivAt hInv.hasFDerivAt
  have hMid := (rectMulCLM m n m).hasFDerivAt_of_bilinear hLeft (hasFDerivAt_const Z M)
  have hQ := (hasFDerivAt_const (1 : Herm m) M).sub
    (rowProjector_differentiableAt_of_inverseGram M hInv).hasFDerivAt
  exact ((rectMulCLM m m m).hasFDerivAt_of_bilinear hMid hQ).differentiableAt

/-- Differentiate the actual explicit tangent matrix field S(N,Z),
holding the variation Z fixed and using the already computed DP. -/
theorem projectorTangent_fderiv_apply_of_inverseGram {n m : ℕ}
    (M Z Y : Rect n m) (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) :
    fderiv ℝ (fun N => projectorTangent N Z) M Y =
      (Yᴴ*(M*Mᴴ)⁻¹-
        Mᴴ*(M*Mᴴ)⁻¹*(M*Yᴴ+Y*Mᴴ)*(M*Mᴴ)⁻¹)*Z*(1-rowProjector M)-
        Mᴴ*(M*Mᴴ)⁻¹*Z*(projectorTangent M Y+(projectorTangent M Y)ᴴ) := by
  have hLeft := (rectMulCLM m n n).hasFDerivAt_of_bilinear
    (rectAdjointCLM n m).hasFDerivAt hInv.hasFDerivAt
  have hMid := (rectMulCLM m n m).hasFDerivAt_of_bilinear hLeft (hasFDerivAt_const Z M)
  have hQ := (hasFDerivAt_const (1 : Herm m) M).sub
    (rowProjector_differentiableAt_of_inverseGram M hInv).hasFDerivAt
  have hProd := (rectMulCLM m m m).hasFDerivAt_of_bilinear hMid hQ
  have hRaw := congrArg (fun L : Rect n m →L[ℝ] Herm m => L Y) hProd.fderiv
  change fderiv ℝ (fun N => projectorTangent N Z) M Y =
    Mᴴ*(M*Mᴴ)⁻¹*Z*((0 : Herm m)-fderiv ℝ rowProjector M Y)+
      (Mᴴ*(M*Mᴴ)⁻¹*(0 : Rect n m)+(Mᴴ*fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Y+
        Yᴴ*(M*Mᴴ)⁻¹)*Z)*(1-rowProjector M) at hRaw
  simp only [zero_sub,Matrix.mul_zero,zero_add] at hRaw
  have hUnit : ∀ᶠ N in 𝓝 M, IsUnit (N*Nᴴ).det := by
    filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
    exact isUnit_iff_ne_zero.mpr hN
  have hID := matrix_inv_fderiv_apply (fun N : Rect n m => N*Nᴴ) M Y
    (gram_hasFDerivAt M).differentiableAt hInv hUnit
  change fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Y =
    -((M*Mᴴ)⁻¹*fderiv ℝ (fun N : Rect n m => N*Nᴴ) M Y*(M*Mᴴ)⁻¹) at hID
  rw [gram_fderiv,gramHessian_apply] at hID
  rw [hRaw,hID,rowProjector_fderiv_apply_of_inverseGram M Y hM hInv]
  simp only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  abel

end Yau.NodeProofs.E02Aux
