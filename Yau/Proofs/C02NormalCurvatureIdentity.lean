import Yau.Proofs.C02NormalCurvatureFrameEquation
import Yau.Proofs.C02CurvatureTensorPairing
import Yau.Proofs.C02CurvatureGauge
import Yau.Proofs.C02NormalDifferentialCoords
import Yau.Proofs.C02ParallelMetricPairing

/-! The curvature in the actual parallel frame is the original fully
covariant Riemann tensor evaluated on the actual normal differential. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalConnectionCurvature_pairing (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x u v w z : ComplexVector n) :
    ⟪normalConnectionCurvature g p U hU x u v w, z⟫_ℝ =
      normalCurvatureJet g p U hU 0 x
        ![normalDifferential g p U hU x u, normalDifferential g p U hU x v, w, z] := by
  let c := normalRealMap g p U x
  have hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hy : normalCoordinateMap g p U c x ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hx)
  have hF := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
    (normalConnectionCurvature_frame_equation g p U hU c x u v hx)
  simp only [ContinuousLinearMap.comp_apply] at hF
  rw [← normalParallelCoefficients_metric_pairing g p U hU c x _ z hx, hF]
  rw [normalCurvatureJet_eq_chart g p U hU c 0 x hx]
  change _ = tensorEvalCLM (rmTensor g.form c (normalCoordinateMap g p U c x))
    (fun i : Fin 4 => normalParallelCoefficients g p U hU c x
      ((![normalDifferential g p U hU x u, normalDifferential g p U hU x v, w, z] :
        Fin 4 → ComplexVector n) i))
  have hVec : (fun i : Fin 4 => normalParallelCoefficients g p U hU c x
      ((![normalDifferential g p U hU x u, normalDifferential g p U hU x v, w, z] :
        Fin 4 → ComplexVector n) i)) =
      ![fderiv ℝ (normalCoordinateMap g p U c) x u,
        fderiv ℝ (normalCoordinateMap g p U c) x v,
        normalParallelCoefficients g p U hU c x w, normalParallelCoefficients g p U hU c x z] := by
    funext i
    fin_cases i
    · exact normalDifferential_coords g p U hU c x u hx
    · exact normalDifferential_coords g p U hU c x v hx
    · rfl
    · rfl
  rw [hVec, tensorEval_rmTensor_pairing g c _ hy]

end Yau.Blueprint.C02Proof
