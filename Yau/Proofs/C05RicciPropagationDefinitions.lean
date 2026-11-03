import Yau.Proofs.C05RealRicciJets
import Yau.Proofs.C05HessianPropagationJets

/-! The physical real Ricci quadratic form and its genuine chart invariance. -/
noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C05RicciPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def ricciQuad (k : HermitianField M) (x : M.Carrier) (v : TangentVector M x) : ℝ :=
  ∑ a : RIdx n, ∑ b : RIdx n,
    realRicciCoeff k x (chartPt x x) a b *
      realCoord (tangentCoords x x v) a * realCoord (tangentCoords x x v) b

theorem ricciQuad_eq_tensor_evaluation (k : HermitianField M) (x : M.Carrier)
    (v w : TangentVector M x) :
    (∑ a : RIdx n, ∑ b : RIdx n,
      realRicciCoeff k x (chartPt x x) a b *
        realCoord (tangentCoords x x v) a * realCoord (tangentCoords x x w) b) =
      tensorEvalCLM (ricciTensor k x (chartPt x x))
        ![tangentCoords x x v,tangentCoords x x w] := by
  rw [tensorEvalCLM_two]
  rfl

theorem ricciTensor_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (v : Fin 2 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => ricciTensor k c z v) (chartTarget c) := by
  change ContDiffOn ℝ ∞ (fun z => realRicciCoeff k c z (v 0) (v 1)) _
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  apply (Yau.LeafProofs.L23Aux.realMetricFn_inverse_contDiffOn k hk c a b).mul
  apply ContDiffOn.sum
  intro l _
  exact (hk c l b).mul (riemannCoeff_contDiffOn k hk c a (v 0) (v 1) l)

theorem ricciTensor_eval_chart_change (k : HermitianField M) (hk : MetricSmooth k)
    (c d : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (hy : chartInv c z ∈ (extChartAt (ComplexModel n) d).source) :
    tensorEvalCLM (ricciTensor k c z) =
      (tensorEvalCLM (ricciTensor k d (realChartChange c d z))).compContinuousLinearMap
        (fun _ : Fin 2 => fderiv ℝ (realChartChange c d) z) := by
  change tensorEvalCLM (fun v : Fin 2 → RIdx n => realRicciCoeff k c z (v 0) (v 1)) = _
  rw [realRicciTensor_chart_change k hk c d hz hy]
  exact tensorEvalCLM_frameTransform _ _

theorem ricciQuad_in_fixed_chart (k : HermitianField M) (hk : MetricSmooth k)
    (c x : M.Carrier)
    (hx : x ∈ (chartAt (ComplexVector n) c).source)
    (u : TangentSpace 𝓘(ℝ,ComplexVector n) x) :
    ricciQuad k x (realTangentEquiv x u) =
      tensorEvalCLM (ricciTensor k c (chartPt c x))
        ![realTangentCoords c x u,realTangentCoords c x u] := by
  have hz : chartPt c x ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source
    (by simpa only [extChartAt_source] using hx)
  have hi : chartInv c (chartPt c x) = x := (extChartAt (ComplexModel n) c).left_inv
    (by simpa only [extChartAt_source] using hx)
  have h := ricciTensor_eval_chart_change k hk c x hz (by rw [hi]; exact mem_extChartAt_source x)
  have he := congrArg (fun A : RealTensorForm n 2 =>
    A ![realTangentCoords c x u,realTangentCoords c x u]) h
  change (∑ a : RIdx n, ∑ b : RIdx n, _ * _ * _) = _
  rw [ricciQuad_eq_tensor_evaluation,tangent_coordinates_real_equiv]
  have hpt : realChartChange c x (chartPt c x) = chartPt x x := by
    change chartPt x (chartInv c (chartPt c x)) = chartPt x x
    rw [hi]
  have hvec : (fun i : Fin 2 => fderiv ℝ (realChartChange c x) (chartPt c x)
      (![realTangentCoords c x u,realTangentCoords c x u] i)) =
        ![realTangentCoords x x u,realTangentCoords x x u] := by
    funext i
    fin_cases i
    · change fderiv ℝ (realChartChange c x) (chartPt c x) (realTangentCoords c x u) = realTangentCoords x x u
      exact realTangentCoords_chart_change c x x hx (mem_chart_source _ _) u
    · change fderiv ℝ (realChartChange c x) (chartPt c x) (realTangentCoords c x u) = realTangentCoords x x u
      exact realTangentCoords_chart_change c x x hx (mem_chart_source _ _) u
  symm
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,hpt,hvec] using he


end Yau.Proofs.C05RicciPropagationAux
