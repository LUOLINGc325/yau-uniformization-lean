import Yau.Proofs.C05HessianPropagationJets
import Yau.LeafProofs.L23TensorEvaluation

/-! Tensor Cauchy--Schwarz with the actual inverse-metric contraction. -/
noncomputable section
open scoped Topology ContDiff Manifold Matrix
namespace Yau.Proofs.C05HessianPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

 theorem tensorEvaluation_three_le
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A : CovTensor n 3) (U V : RIdx n → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hA : Real.sqrt (covTensorNormSq G A) ≤ C) :
    |tensorEvaluation A ![U,V,V]| ≤
      C * Real.sqrt (U ⬝ᵥ (G *ᵥ U)) * (V ⬝ᵥ (G *ᵥ V)) := by
  have hU : 0 ≤ U ⬝ᵥ (G *ᵥ U) := by
    simpa only [star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg U
  have hV : 0 ≤ V ⬝ᵥ (G *ᵥ V) := by
    simpa only [star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg V
  have hN : 0 ≤ covTensorNormSq G A := covTensorNormSq_nonneg G hG A
  have hNle : covTensorNormSq G A ≤ C ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr hA
    rwa [Real.sq_sqrt hN] at h
  have hcauchy := tensorEvaluation_sq_le G hG A ![U,V,V]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,mul_one] at hcauchy
  apply (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) hV)).mp
  rw [sq_abs]
  calc
    _ ≤ covTensorNormSq G A * ((U ⬝ᵥ (G *ᵥ U)) * ((V ⬝ᵥ (G *ᵥ V)) * (V ⬝ᵥ (G *ᵥ V)))) := hcauchy
    _ ≤ C ^ 2 * ((U ⬝ᵥ (G *ᵥ U)) * ((V ⬝ᵥ (G *ᵥ V)) * (V ⬝ᵥ (G *ᵥ V)))) :=
      mul_le_mul_of_nonneg_right hNle (mul_nonneg hU (mul_nonneg hV hV))
    _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hU]; ring

 theorem scalarJetNorm_sq (k : HermitianField M) (f : M.Carrier → ℝ)
    (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k f m x ^ 2 = covTensorNormSq (realMetricFn k x (chartPt x x))
      (scalarJet k f x m (chartPt x x)) :=
  Real.sq_sqrt (covTensorNormSq_nonneg _
    (realMetricFn_posDef k x _ (mem_extChartAt_target x)) _)

 theorem real_metric_coordinates_normSq (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    (fun a => realCoord (tangentCoords x x v) a) ⬝ᵥ
      (realMetricFn k x (chartPt x x) *ᵥ (fun a => realCoord (tangentCoords x x v) a)) =
        realNormSq k x v := by
  have hi : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have H := realMetricFn_quadratic k x (chartPt x x)
    (fun a => realCoord (tangentCoords x x v) a)
  rw [sum_realCoord_realVec,hi,chartVec_tangentCoords x x (mem_extChartAt_source x)] at H
  simpa only [star_trivial,hermitianRealBilin_apply,realNormSq,hermitianNormSq] using H

 theorem scalarJet_three_evaluation_le
    (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier)
    (u v : TangentVector M x) {C : ℝ} (hC : 0 ≤ C)
    (hthird : scalarJetNorm k f 3 x ≤ C) :
    |tensorEvalCLM (scalarJet k f x 3 (chartPt x x))
      ![tangentCoords x x u,tangentCoords x x v,tangentCoords x x v]| ≤
      C * realNorm k x u * realNormSq k x v := by
  have H := tensorEvaluation_three_le (realMetricFn k x (chartPt x x))
    (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (scalarJet k f x 3 (chartPt x x))
    (fun a => realCoord (tangentCoords x x u) a)
    (fun a => realCoord (tangentCoords x x v) a) hC hthird
  rw [real_metric_coordinates_normSq,real_metric_coordinates_normSq] at H
  have hvec : (fun j : Fin 3 => fun a => realCoord
      (![tangentCoords x x u,tangentCoords x x v,tangentCoords x x v] j) a) =
      ![fun a => realCoord (tangentCoords x x u) a,
        fun a => realCoord (tangentCoords x x v) a,
        fun a => realCoord (tangentCoords x x v) a] := by
    funext j
    fin_cases j <;> rfl
  rw [← hvec] at H
  simpa only [tensorEvalCLM_apply,tensorEvaluation,tensorProduct,realNorm] using H

end Yau.Proofs.C05HessianPropagationAux
