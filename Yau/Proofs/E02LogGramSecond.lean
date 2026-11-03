import Yau.Proofs.E02InverseDerivative
import Yau.Proofs.E02GramRegularity

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance logGramRectNormable (n m : ℕ) : IsNormableSpace ℝ (Rect n m) :=
  inferInstanceAs (IsNormableSpace ℝ (Fin n → Fin m → ℂ))

def matrixTraceRealCLM (n : ℕ) : Herm n →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap

/-- Differentiate the actual first log-Gram derivative on its open
full-rank neighborhood. The smoothness and first-derivative hypotheses
are ordinary calculus inputs later supplied for the literal logdet. -/
theorem second_fderiv_of_gram_logderivative {n m : ℕ} (f : Rect n m → ℝ)
    (M Y Z : Rect n m) (hM : (M*Mᴴ).PosDef) (hf : ContDiffAt ℝ 2 f M)
    (hInv : DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M)
    (hFirst : ∀ᶠ N in 𝓝 M, ∀ V : Rect n m,
      fderiv ℝ f N V = (Matrix.trace ((N*Nᴴ)⁻¹*(N*Vᴴ+V*Nᴴ))).re) :
    fderiv ℝ (fderiv ℝ f) M Y Z =
      (Matrix.trace ((M*Mᴴ)⁻¹*(Y*Zᴴ+Z*Yᴴ)-
        (M*Mᴴ)⁻¹*(M*Yᴴ+Y*Mᴴ)*(M*Mᴴ)⁻¹*(M*Zᴴ+Z*Mᴴ))).re := by
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF2 := congrArg (fun L : Rect n m →L[ℝ] ℝ => L Y)
    (hDf.hasFDerivAt.clm_apply (hasFDerivAt_const Z M)).fderiv
  change fderiv ℝ (fun N : Rect n m => fderiv ℝ f N Z) M Y =
    fderiv ℝ f M (0 : Rect n m)+fderiv ℝ (fderiv ℝ f) M Y Z at hF2
  simp only [map_zero,zero_add] at hF2
  have hEq : (fun N : Rect n m => fderiv ℝ f N Z) =ᶠ[𝓝 M]
      (fun N : Rect n m => (Matrix.trace ((N*Nᴴ)⁻¹*(N*Zᴴ+Z*Nᴴ))).re) := by
    filter_upwards [hFirst] with N hN
    exact hN Z
  have hDir : HasFDerivAt (fun N : Rect n m => N*Zᴴ+Z*Nᴴ)
      ((gramHessian n m).flip Z) M := (gramHessian n m).flip Z |>.hasFDerivAt
  have hProd := (rectMulCLM n n n).hasFDerivAt_of_bilinear hInv.hasFDerivAt hDir
  have hTrace := (matrixTraceRealCLM n).hasFDerivAt.comp M hProd
  have hValue := congrArg (fun L : Rect n m →L[ℝ] ℝ => L Y) hTrace.fderiv
  change fderiv ℝ (fun N : Rect n m => (Matrix.trace ((N*Nᴴ)⁻¹*(N*Zᴴ+Z*Nᴴ))).re) M Y =
    (Matrix.trace ((M*Mᴴ)⁻¹*(Y*Zᴴ+Z*Yᴴ)+
      fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Y*(M*Zᴴ+Z*Mᴴ))).re at hValue
  have hUnit : ∀ᶠ N in 𝓝 M, IsUnit (N*Nᴴ).det := by
    filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
    exact isUnit_iff_ne_zero.mpr hN
  have hID := matrix_inv_fderiv_apply (fun N : Rect n m => N*Nᴴ) M Y
    (gram_hasFDerivAt M).differentiableAt hInv hUnit
  change fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Y =
    -((M*Mᴴ)⁻¹*fderiv ℝ (fun N : Rect n m => N*Nᴴ) M Y*(M*Mᴴ)⁻¹) at hID
  rw [gram_fderiv,gramHessian_apply] at hID
  rw [hID,Matrix.neg_mul,←sub_eq_add_neg] at hValue
  exact hF2.symm.trans ((congrArg (fun L : Rect n m →L[ℝ] ℝ => L Y)
    (hEq.fderiv_eq (𝕜 := ℝ))).trans hValue)

end Yau.NodeProofs.E02Aux
