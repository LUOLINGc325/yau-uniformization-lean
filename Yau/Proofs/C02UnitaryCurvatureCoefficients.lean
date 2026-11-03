import Yau.Proofs.C02UnitaryChernReal
import Yau.Proofs.C02PhysicalTensorFrame
import Yau.Proofs.C02TensorRmEvaluation
import Yau.Proofs.C02CurvatureCoefficientNorm
import Yau.Proofs.C02UnitaryCurvatureNorm

noncomputable section
open scoped Matrix InnerProductSpace Manifold
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem physicalCurvatureFrame_eq_coefficientVector (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p) (I : Fin 4 → RIdx n) :
    tensorFrameTransform (physicalUnitaryRealMatrix (unitaryFrameMatrix p U))
      (rmTensor g.form p (chartPt p p)) I =
        realCurvatureCoefficientLinear n (unitaryChernArray g.form p U) I := by
  let S := unitaryFrameMatrix p U
  have hTuple : (fun j : Fin 4 => complexMatrixVector S (realVec (I j))) =
      ![complexMatrixVector S (realVec (I 0)), complexMatrixVector S (realVec (I 1)),
        complexMatrixVector S (realVec (I 2)), complexMatrixVector S (realVec (I 3))] := by
    funext j
    fin_cases j <;> rfl
  have hs2 : (Real.sqrt (2 : ℝ))⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hs4 : (Real.sqrt (2 : ℝ))⁻¹ ^ 4 = 1 / 4 := by
    calc
      _ = ((Real.sqrt (2 : ℝ))⁻¹ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs2]; norm_num
  change _ = (1 / 4 : ℝ) * realCurvatureEvaluation (unitaryChernArray g.form p U)
    (WithLp.ofLp (realVec (I 0))) (WithLp.ofLp (realVec (I 1)))
    (WithLp.ofLp (realVec (I 2))) (WithLp.ofLp (realVec (I 3)))
  rw [tensorFrameTransform_physicalUnitary, hTuple,
    tensorEval_rmTensor_eq_realRmInChart g p (chartPt p p) (mem_extChartAt_target p)]
  rw [← unitaryChernArray_real_evaluation g p U, hs4]

theorem curvatureJetNorm_zero_eq_unitaryChern_norm (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    curvatureJetNorm g.form 0 p = ‖realCurvatureCoefficientLinear n (unitaryChernArray g.form p U)‖ := by
  rw [curvatureJetNorm_zero_eq_unitary_frame_norm g.form p U hU]
  congr 1
  ext I
  exact physicalCurvatureFrame_eq_coefficientVector g p U I

end Yau.Blueprint.C02Proof
