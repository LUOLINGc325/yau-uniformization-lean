import Yau.Proofs.C02ChristoffelCurvature
import Yau.Proofs.C02TensorFourEvaluation

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem tensorEval_rmTensor_pairing (g : SmoothMetric M) (c : M.Carrier)
    (y : ComplexVector n) (hy : y ∈ chartTarget c) (u v w z : ComplexVector n) :
    tensorEvalCLM (rmTensor g.form c y) ![u, v, w, z] =
      realMetricInChart g.form c y
        (connectionCurvature (chartChristoffelBilin g.form c) y u v w) z := by
  have hBasis (a b k d : RIdx n) :
      tensorEvalCLM (rmTensor g.form c y) ![realVec a, realVec b, realVec k, realVec d] =
        curvature4 g.form c y a b k d := by
    have he : ![realVec a, realVec b, realVec k, realVec d] =
        (fun i : Fin 4 => realVec ((![a, b, k, d] : Fin 4 → RIdx n) i)) := by
      funext i
      fin_cases i <;> rfl
    rw [he, tensorEvalCLM_basis]
    rfl
  rw [tensorFour_eval_sum]
  simp_rw [hBasis]
  rw [chartConnectionCurvature_eq]
  exact (chartCurvaturePairing_eq_sum g c y hy u v w z).symm

end Yau.Blueprint.C02Proof
