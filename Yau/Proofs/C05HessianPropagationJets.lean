import Yau.Proofs.C05ScalarJetDefinitions
import Yau.LeafProofs.L23TensorChart

/-! The actual scalar covariant jets are smooth tensor fields in every chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05HessianPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarJet_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier) (m : ℕ)
    (v : Fin m → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => scalarJet k f c m z v) (chartTarget c) := by
  induction m with
  | zero => exact hf c
  | succ m ih => exact covariantD_contDiffOn k hk c (scalarJet k f c m) ih v

theorem scalarJet_eval_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (m : ℕ) (c d : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (scalarJet k f c m z) =
      (tensorEvalCLM (scalarJet k f d m (realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin m => fderiv ℝ (realChartChange c d) z) := by
  induction m generalizing z with
  | zero =>
    have heq : inChart c f z = inChart d f (realChartChange c d z) := by
      change f (chartInv c z) = f (chartInv d (chartPt d (chartInv c z)))
      exact (congrArg f ((extChartAt (ComplexModel n) d).left_inv hy)).symm
    ext V
    simpa only [tensorEvalCLM_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,
      scalarJet,Fin.prod_univ_zero,Fintype.sum_unique,mul_one] using heq
  | succ m ih =>
    apply covariantD_chart_change k hk c d (scalarJet k f c m) (scalarJet k f d m) hz hy
    · intro v
      exact ((scalarJet_contDiffOn k hk f hf c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
    · intro v
      have hd : realChartChange c d z ∈ chartTarget d :=
        (extChartAt (ComplexModel n) d).map_source hy
      exact ((scalarJet_contDiffOn k hk f hf d m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) d).mem_nhds hd)).differentiableAt (by simp)
    · intro w hw
      exact ih hw.1 hw.2

theorem tensorEvalCLM_two (A : CovTensor n 2) (u v : ComplexVector n) :
    tensorEvalCLM A ![u,v] =
      ∑ a : RIdx n, ∑ b : RIdx n, A ![a,b] * realCoord u a * realCoord v b := by
  rw [tensorEvalCLM_apply]
  rw [← (finTwoArrowEquiv (RIdx n)).symm.sum_comp]
  simp only [Fintype.sum_prod_type,finTwoArrowEquiv,Equiv.coe_fn_symm_mk,
    Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,Matrix.cons_val_zero,
    Matrix.cons_val_succ,mul_assoc]

theorem realHess_eq_scalarJet_evaluation (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) (v w : TangentVector M x) :
    realHess k f x v w = tensorEvalCLM (scalarJet k f x 2 (chartPt x x))
      ![tangentCoords x x v,tangentCoords x x w] := by
  rw [tensorEvalCLM_two]
  simp only [scalarJet_two,realHess]

theorem tangent_coordinates_real_equiv (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ,ComplexVector n) x) :
    tangentCoords x x (realTangentEquiv x v) = realTangentCoords x x v := by
  rw [realTangentCoords_self]
  have H := tangentCoords_chartVec x x (mem_extChartAt_source x)
    ((tangentSpaceCastModel 𝓘(ℝ,ComplexVector n) x) v)
  rw [chartVec_self] at H
  exact H

theorem realTangentCoords_chart_change (c d x : M.Carrier)
    (hc : x ∈ (chartAt (ComplexVector n) c).source)
    (hd : x ∈ (chartAt (ComplexVector n) d).source)
    (v : TangentSpace 𝓘(ℝ,ComplexVector n) x) :
    fderiv ℝ (realChartChange c d) (chartPt c x) (realTangentCoords c x v) =
      realTangentCoords d x v := by
  have hz : chartPt c x ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source
    (by simpa only [extChartAt_source] using hc)
  have hi : chartInv c (chartPt c x) = x := (extChartAt (ComplexModel n) c).left_inv
    (by simpa only [extChartAt_source] using hc)
  have hx : chartInv c (chartPt c x) ∈ (extChartAt (ComplexModel n) d).source := by
    rw [hi]
    simpa only [extChartAt_source] using hd
  have H := realChartChange_fderiv c d hz hx (realTangentCoords c x v)
  rw [hi,← realFrameCLM_apply c x hc,realFrameCLM_realTangentCoords c x hc] at H
  exact H

theorem realHess_in_fixed_chart (k : HermitianField M) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c x : M.Carrier)
    (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (u v : TangentSpace 𝓘(ℝ,ComplexVector n) x) :
    realHess k f x (realTangentEquiv x u) (realTangentEquiv x v) =
      tensorEvalCLM (scalarJet k f c 2 (chartPt c x))
        ![realTangentCoords c x u,realTangentCoords c x v] := by
  have hz : chartPt c x ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source
    (by simpa only [extChartAt_source] using hx)
  have hi : chartInv c (chartPt c x) = x := (extChartAt (ComplexModel n) c).left_inv
    (by simpa only [extChartAt_source] using hx)
  have h := scalarJet_eval_chart_change k hk f hf 2 c x hz (by rw [hi]; exact mem_extChartAt_source x)
  have he := congrArg (fun A : RealTensorForm n 2 =>
    A ![realTangentCoords c x u,realTangentCoords c x v]) h
  rw [realHess_eq_scalarJet_evaluation,tangent_coordinates_real_equiv,tangent_coordinates_real_equiv]
  have hpt : realChartChange c x (chartPt c x) = chartPt x x := by
    change chartPt x (chartInv c (chartPt c x)) = chartPt x x
    rw [hi]
  have hvec : (fun i : Fin 2 => fderiv ℝ (realChartChange c x) (chartPt c x)
      (![realTangentCoords c x u,realTangentCoords c x v] i)) =
        ![realTangentCoords x x u,realTangentCoords x x v] := by
    funext i
    fin_cases i
    · change fderiv ℝ (realChartChange c x) (chartPt c x) (realTangentCoords c x u) = realTangentCoords x x u
      exact realTangentCoords_chart_change c x x hx (mem_chart_source _ _) u
    · change fderiv ℝ (realChartChange c x) (chartPt c x) (realTangentCoords c x v) = realTangentCoords x x v
      exact realTangentCoords_chart_change c x x hx (mem_chart_source _ _) v
  symm
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hpt,hvec] using he

end Yau.Proofs.C05HessianPropagationAux
