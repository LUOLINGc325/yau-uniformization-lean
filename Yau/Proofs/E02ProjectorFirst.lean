import Yau.Proofs.E02InverseDerivative
import Yau.Proofs.E02GramRegularity
import Yau.Proofs.E02GrassmannAlgebra

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem projectorTangent_conjTranspose {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    (projectorTangent M Z)ᴴ = (1-rowProjector M)*Zᴴ*(M*Mᴴ)⁻¹*M := by
  rw [projectorTangent,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    hM.inv.isHermitian.eq]
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,(rowProjector_isHermitian M hM).eq]
  simp only [Matrix.mul_assoc]

theorem projectorTangent_smul_direction {n m : ℕ} (M Z : Rect n m) (c : ℂ) :
    projectorTangent M (c • Z) = c • projectorTangent M Z := by
  simp only [projectorTangent,Matrix.mul_smul,Matrix.smul_mul]

/-- Ordinary differentiability is proved from that of the actual inverse
Gram field; the latter will be supplied on the open full-rank locus. -/
theorem rowProjector_differentiableAt_of_inverseGram {n m : ℕ} (M : Rect n m)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) :
    DifferentiableAt ℝ (rowProjector (n := n) (m := m)) M := by
  have hLeft := (rectMulCLM m n n).hasFDerivAt_of_bilinear
    (rectAdjointCLM n m).hasFDerivAt hInv.hasFDerivAt
  exact ((rectMulCLM m n m).hasFDerivAt_of_bilinear hLeft (hasFDerivAt_id M)).differentiableAt

/-- This differentiates the original explicit orthogonal projector.
The right-hand side is derived from the inverse identity and product rule. -/
theorem rowProjector_fderiv_apply_of_inverseGram {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M) :
    fderiv ℝ rowProjector M Z = projectorTangent M Z+(projectorTangent M Z)ᴴ := by
  have hUnit : ∀ᶠ N in 𝓝 M, IsUnit (N*Nᴴ).det := by
    filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
    exact isUnit_iff_ne_zero.mpr hN
  have hLeft := (rectMulCLM m n n).hasFDerivAt_of_bilinear
    (rectAdjointCLM n m).hasFDerivAt hInv.hasFDerivAt
  have hProd := (rectMulCLM m n m).hasFDerivAt_of_bilinear hLeft (hasFDerivAt_id M)
  have hRaw := congrArg (fun L : Rect n m →L[ℝ] Herm m => L Z) hProd.fderiv
  change fderiv ℝ rowProjector M Z =
    Mᴴ*(M*Mᴴ)⁻¹*Z+
      (Mᴴ*fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Z+Zᴴ*(M*Mᴴ)⁻¹)*M at hRaw
  have hID := matrix_inv_fderiv_apply (fun N : Rect n m => N*Nᴴ) M Z
    (gram_hasFDerivAt M).differentiableAt hInv hUnit
  change fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Z =
    -((M*Mᴴ)⁻¹*fderiv ℝ (fun N : Rect n m => N*Nᴴ) M Z*(M*Mᴴ)⁻¹) at hID
  rw [gram_fderiv,gramHessian_apply] at hID
  rw [hID] at hRaw
  rw [hRaw,projectorTangent_conjTranspose M Z hM]
  unfold projectorTangent rowProjector
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_one,Matrix.one_mul,Matrix.mul_assoc]
  abel

end Yau.NodeProofs.E02Aux
