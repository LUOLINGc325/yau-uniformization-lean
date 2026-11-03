import Yau.Proofs.C02ChernScalarTrace
import Yau.Proofs.C02ChernRealEvaluation
import Yau.Proofs.C02RealFrameCoordinates

noncomputable section
open scoped Matrix Manifold InnerProductSpace
namespace Yau.Blueprint.C02Proof
open Yau.NodeProofs.G01Aux Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem unitaryChernArray_real_evaluation (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (u v w z : ComplexVector n) :
    realCurvatureEvaluation (unitaryChernArray g.form p U)
      (WithLp.ofLp u) (WithLp.ofLp v) (WithLp.ofLp w) (WithLp.ofLp z) =
      realRmInChart g.form p (chartPt p p)
        (complexMatrixVector (unitaryFrameMatrix p U) u)
        (complexMatrixVector (unitaryFrameMatrix p U) v)
        (complexMatrixVector (unitaryFrameMatrix p U) w)
        (complexMatrixVector (unitaryFrameMatrix p U) z) := by
  let S := unitaryFrameMatrix p U
  let C := curvatureBasisTransform (actualChernArray g.form p) S
  have hS (a : ComplexVector n) : S *ᵥ WithLp.ofLp a = WithLp.ofLp (complexMatrixVector S a) :=
    funext (fun i => (complexMatrixVector_apply S a i).symm)
  have hRaw (a b c d : ComplexVector n) :
      realCurvatureEvaluation C (WithLp.ofLp a) (WithLp.ofLp b) (WithLp.ofLp c) (WithLp.ofLp d) =
      realRmInChart g.form p (chartPt p p) (complexMatrixVector S a) (complexMatrixVector S b)
        (complexMatrixVector S c) (complexMatrixVector S d) := by
    dsimp only [C]
    rw [realCurvatureEvaluation_basisTransform, hS a, hS b, hS c, hS d]
    exact actualChernArray_real_evaluation g.form (metricSmooth_of_smoothMetric g) g.kahler_equations p _ _ _ _
  have hSkew : realCurvatureEvaluation C (WithLp.ofLp u) (WithLp.ofLp v) (WithLp.ofLp z) (WithLp.ofLp w) =
      -realCurvatureEvaluation C (WithLp.ofLp u) (WithLp.ofLp v) (WithLp.ofLp w) (WithLp.ofLp z) := by
    rw [hRaw, hRaw]
    exact realRmInChart_swap_last g p (chartPt p p) (mem_extChartAt_target p) _ _ _ _
  exact (realCurvatureEvaluation_hermitianPart C _ _ _ _ hSkew).trans (hRaw u v w z)

end Yau.Blueprint.C02Proof
