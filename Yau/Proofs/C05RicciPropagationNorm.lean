import Yau.Proofs.C05RicciPropagationDefinitions
import Yau.Proofs.C05HessianPropagationNorm

/-! The actual rank-three Ricci derivative with physical metric Cauchy--Schwarz. -/
noncomputable section
open scoped Topology ContDiff Manifold Matrix
namespace Yau.Proofs.C05RicciPropagationAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05GradientFlowAux
open Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
 theorem ricciJet_one_evaluation_le
    (k : HermitianField M) (x : M.Carrier)
    (u v : TangentVector M x) {C : ℝ} (hC : 0 ≤ C)
    (hthird : realRicciJetNorm k 1 x ≤ C) :
    |tensorEvalCLM (realRicciJet k x 1 (chartPt x x))
      ![tangentCoords x x u,tangentCoords x x v,tangentCoords x x v]| ≤
      C * realNorm k x u * realNormSq k x v := by
  have H := tensorEvaluation_three_le (realMetricFn k x (chartPt x x))
    (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (realRicciJet k x 1 (chartPt x x))
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


end Yau.Proofs.C05RicciPropagationAux
