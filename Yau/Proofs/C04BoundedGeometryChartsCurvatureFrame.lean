import Yau.Proofs.C04BoundedGeometryChartsTensorBounds
import Yau.Proofs.C04BoundedGeometryChartsRadialFrame
import Yau.Proofs.P02BisectionalNaturality

/-! Actual covariant curvature jets in the actual radial parallel frame. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem real_tangent_metric_coordinates (k : HermitianField M) (x : M.Carrier)
    (V : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    realCoord (realTangentCoords x x V) ⬝ᵥ
      (realMetricFn k x (chartPt x x) *ᵥ realCoord (realTangentCoords x x V)) =
      (underlyingRealRiemannianMetric k).inner x V V := by
  have H := realMetricInChart_quadratic_eq_matrix k x (mem_extChartAt_target x)
    (realTangentCoords x x V)
  exact H.symm.trans (realMetricInChart_tangentCoords k x x (mem_chart_source _ _) V V)

def radialCurvatureCoefficients (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (v : ComplexVector n) :
    CovTensor n (4 + m) :=
  fun idx =>
    let x := unitaryExponential g p U v
    tensorEvaluation (rmJet g.form x m (chartPt x x))
      (fun j => realCoord (realTangentCoords x x (radialParallelFrame g p U v (realVec (idx j)))))

theorem radialCurvatureCoefficients_abs_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (m : ℕ) (v : ComplexVector n) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : curvatureJetNorm g.form m (unitaryExponential g p U v) ≤ K)
    (idx : Fin (4 + m) → RIdx n) :
    |radialCurvatureCoefficients g p U m v idx| ≤ K * Real.sqrt 2 ^ (4 + m) := by
  apply curvature_jet_frame_evaluation_le g.form (unitaryExponential g p U v) m _ hK
    (Real.sqrt_nonneg 2) hcurv
  intro j
  rw [real_tangent_metric_coordinates, radialParallelFrame_metric g p U hU]
  have hnorm (a : RIdx n) : ‖realVec a‖ = 1 := by
    rcases a with ⟨i, a⟩
    fin_cases a <;> simp [realVec, norm_smul]
  have hinner (a : RIdx n) : (⟪realVec a, realVec a⟫_ℂ).re = 1 := by
    calc
      _ = ‖realVec a‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) (realVec a)).symm
      _ = 1 := by rw [hnorm]; norm_num
  rw [hinner, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end Yau.Proofs.C04ChartsAux
