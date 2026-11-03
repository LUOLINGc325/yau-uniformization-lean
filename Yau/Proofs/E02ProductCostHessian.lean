import Yau.Proofs.E02ProductCost
import Yau.Proofs.E02CoordinateSecond
import Yau.Proofs.E02SecondLinearRules

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem productCostPhysical_second_apply {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q U V : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    fderiv ℝ (fderiv ℝ (productCostPhysical f α P₀ θ)) Q U V =
      fderiv ℝ (fderiv ℝ f) (Q.1,Q.2.1) (U.1,U.2.1) (V.1,V.2.1)+
      fderiv ℝ (fderiv ℝ logGram) (weightedColumns α Q.2.2)
        (weightedColumns α U.2.2) (weightedColumns α V.2.2)-
      θ*fderiv ℝ (fderiv ℝ (projectorPenalty (n := n) P₀)) (weightedColumns α Q.2.2)
        (weightedColumns α U.2.2) (weightedColumns α V.2.2) := by
  let L₁ := productBaseTimeCLM n m
  let L₂ : ProductPoint n m →L[ℝ] Rect n m := productColumnsCLM α
  have hBase : ContDiffAt ℝ 2 f (L₁ Q) := hf
  have hLog : ContDiffAt ℝ 2 logGram (L₂ Q) :=
    ((logGram_contDiffOn n m).contDiffAt ((isOpen_fullRankRect n m).mem_nhds
      ((fullRankRect_iff_posDef _).mpr hM))).of_le (by simp)
  have hPenalty : ContDiffAt ℝ 2 (projectorPenalty (n := n) P₀) (L₂ Q) :=
    (projectorPenalty_contDiffAt P₀ _ hM).of_le (by simp)
  have hBaseComp := hBase.comp Q L₁.contDiff.contDiffAt
  have hLogComp := hLog.comp Q L₂.contDiff.contDiffAt
  have hPenComp := hPenalty.comp Q L₂.contDiff.contDiffAt
  have hSum := second_fderiv_const_add_add_sub_mul hBaseComp hLogComp hPenComp (n : ℝ) θ
  have hVal := congrArg (fun A : ProductPoint n m →L[ℝ] ProductPoint n m →L[ℝ] ℝ => A U V) hSum
  simp only [_root_.add_apply,_root_.sub_apply,_root_.smul_apply,smul_eq_mul,Function.comp_def] at hVal
  erw [second_fderiv_linear_comp_apply L₁ hBase U V,
    second_fderiv_linear_comp_apply L₂ hLog U V,
    second_fderiv_linear_comp_apply L₂ hPenalty U V] at hVal
  convert hVal using 1 <;> rfl

theorem productCostPacked_second_apply {n m : ℕ} (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ) (Q U V : ProductPoint n m)
    (hf : ContDiffAt ℝ 2 f (Q.1,Q.2.1))
    (hM : (weightedColumns α Q.2.2*(weightedColumns α Q.2.2)ᴴ).PosDef) :
    fderiv ℝ (fderiv ℝ (productCostPacked f α P₀ θ)) (productRealCoordinates n m Q)
        (productRealCoordinates n m U) (productRealCoordinates n m V) =
      fderiv ℝ (fderiv ℝ (productCostPhysical f α P₀ θ)) Q U V :=
  continuousLinearEquiv_second_fderiv_apply (productRealCoordinates n m)
    (productCostPhysical_contDiffAt f α P₀ θ Q hf hM) U V

end Yau.NodeProofs.E02Aux
