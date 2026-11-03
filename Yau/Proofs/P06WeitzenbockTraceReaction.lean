import Yau.Proofs.P06WeitzenbockComputedReaction
import Yau.Proofs.P06WeitzenbockTraceConnection
import Yau.Proofs.P06WeitzenbockTypeCurvature

noncomputable section
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs G04Aux L12Aux G01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem relativeKernel_trace_zero
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (H A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (H * (finiteCurvatureAction R H * H * A + A * H * finiteCurvatureAction R H -
      (2 : ℂ) • finiteCurvatureAction R (H * A * H))) = 0 := by
  have hc := finiteCurvatureAction_trace_selfadjoint R hR H (H * A * H)
  have h₁ : Matrix.trace (H * (finiteCurvatureAction R H * H * A)) =
      Matrix.trace (H * A * H * finiteCurvatureAction R H) := by
    calc
      _ = Matrix.trace ((H * finiteCurvatureAction R H) * (H * A)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((H * A) * (H * finiteCurvatureAction R H)) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  have h₂ : Matrix.trace (H * (A * H * finiteCurvatureAction R H)) =
      Matrix.trace (H * A * H * finiteCurvatureAction R H) := by congr 1; noncomm_ring
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h₁, h₂, hc]
  ring

theorem hermitianReaction_trace_zero (g : SmoothMetric M) (hk : IsKahler g)
    (A : RealForm M 2) (x : M.Carrier) :
    Matrix.trace ((gMat g.form x)⁻¹ * hermitianCurvatureReaction g.form A x) = 0 := by
  rw [hermitianCurvatureReaction,
    computedRicci_eq_curvatureAction g.form (L12Aux.metricSmooth_of_smoothMetric g) hk x]
  exact relativeKernel_trace_zero (chernCurvature g.form x)
    (computedChern_pair g.form (L12Aux.metricSmooth_of_smoothMetric g) hk x)
    (gMat g.form x)⁻¹ (formHermitianMatrix A x)

theorem matrixMetricJTrace_raw (h : HermitianField M) (x : M.Carrier)
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    matrixMetricJTrace (realMetricFn h x (chartPt x x))⁻¹
      ((-2 : ℝ) • (rawReal Q * jMatrix n)) =
      (Matrix.trace ((gMat h x)⁻¹ * Q)).re := by
  rw [matrixMetricJTrace, realMetricFn_inverse_eq h x (chartPt x x) (mem_extChartAt_target x)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num only [show (1 / 2 : ℝ) * (-2) = -1 by norm_num, neg_one_smul]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, jMatrix_sq]
  simp only [Matrix.mul_neg, Matrix.mul_one, neg_neg]
  rw [← rawReal_mul, rawReal_trace]
  dsimp only [gMat]
  ring

theorem trace_curvature_zero (g : SmoothMetric M) (hk : IsKahler g)
    (A : RealForm M 2) (h11 : RealOneOne A) (x : M.Carrier) :
    matrixMetricJTrace (realMetricFn g.form x (chartPt x x))⁻¹
      (curvatureTwoMatrix g.form A x (chartPt x x)) = 0 := by
  have he := curvatureTwoMatrix_eq_raw_reaction g hk A h11 x
  change curvatureTwoMatrix g.form A x (chartPt x x) = _ at he
  rw [he, matrixMetricJTrace_raw, hermitianReaction_trace_zero g hk A x]
  rfl

end Yau.NodeProofs.P06Weitzenbock
