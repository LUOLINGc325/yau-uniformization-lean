import Yau.Proofs.C02CurvatureTensorPairing
import Yau.Proofs.G01RmAlgebra

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux Yau.NodeProofs.G01Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem tensorEval_rmTensor_eq_realRmInChart (g : SmoothMetric M) (p : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget p) (u v w z : ComplexVector n) :
    tensorEvalCLM (rmTensor g.form p y) ![u, v, w, z] = realRmInChart g.form p y u v w z := by
  rw [tensorEval_rmTensor_pairing g p y hy, chartConnectionCurvature_eq,
    chartCurvaturePairing_eq_sum g p y hy]
  unfold realRmInChart
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

end Yau.Blueprint.C02Proof
