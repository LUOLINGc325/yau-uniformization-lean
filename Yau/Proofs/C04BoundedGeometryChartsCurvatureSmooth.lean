import Yau.Proofs.C04BoundedGeometryChartsCoframeSmooth
import Yau.Proofs.C04BoundedGeometryChartsCurvatureFrame

/-! The intrinsic curvature jets expressed in the actual radial frame are smooth functions. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem tensorEvalCLM_eq_tensorEvaluation (A : CovTensor n r) (V : Fin r → ComplexVector n) :
    tensorEvalCLM A V = tensorEvaluation A (fun j => realCoord (V j)) := by
  rw [tensorEvalCLM_apply]
  rfl

theorem rmJet_realTangent_chart_change (g : SmoothMetric M) (m : ℕ)
    (c d y : M.Carrier)
    (hc : y ∈ (chartAt (ComplexVector n) c).source)
    (hd : y ∈ (chartAt (ComplexVector n) d).source)
    (V : Fin (4 + m) → TangentSpace 𝓘(ℝ, ComplexVector n) y) :
    tensorEvalCLM (rmJet g.form c m (chartPt c y)) (fun j => realTangentCoords c y (V j)) =
      tensorEvalCLM (rmJet g.form d m (chartPt d y)) (fun j => realTangentCoords d y (V j)) := by
  have hc' : y ∈ (extChartAt (ComplexModel n) c).source := by
    simpa only [extChartAt_source] using hc
  have hd' : y ∈ (extChartAt (ComplexModel n) d).source := by
    simpa only [extChartAt_source] using hd
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hc'
  have hinv : chartInv c (chartPt c y) = y := (extChartAt (ComplexModel n) c).left_inv hc'
  have hy : chartInv c (chartPt c y) ∈ (extChartAt (ComplexModel n) d).source := by rwa [hinv]
  have hD (Z : TangentSpace 𝓘(ℝ, ComplexVector n) y) :
      fderiv ℝ (realChartChange c d) (chartPt c y) (realTangentCoords c y Z) =
        realTangentCoords d y Z := by
    rw [realChartChange_fderiv c d hz hy, hinv,
      ← realFrameCLM_apply c y hc, realFrameCLM_realTangentCoords c y hc]
  rw [rmJet_eval_chart_change g.form (metricSmooth_of_smoothMetric g) m c d hz hy,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hch : realChartChange c d (chartPt c y) = chartPt d y := by
    change chartPt d (chartInv c (chartPt c y)) = _
    rw [hinv]
  rw [hch]
  congr 1
  funext j
  exact hD (V j)

theorem radialCurvatureCoefficients_in_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (c : M.Carrier)
    (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source)
    (idx : Fin (4 + m) → RIdx n) :
    radialCurvatureCoefficients g p U m v idx =
      tensorEvaluation (rmJet g.form c m (chartPt c (unitaryExponential g p U v)))
        (fun j => realCoord (radialFrameCoordinates g p U c v (realVec (idx j)))) := by
  have H := rmJet_realTangent_chart_change g m (unitaryExponential g p U v) c
    (unitaryExponential g p U v) (mem_chart_source _ _) hc
    (fun j => radialParallelFrame g p U v (realVec (idx j)))
  simpa only [tensorEvalCLM_eq_tensorEvaluation, radialCurvatureCoefficients,
    radialFrameCoordinates, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using H

theorem radialCurvatureCoefficients_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) :
    ContDiff ℝ ∞ (radialCurvatureCoefficients g p U m) := by
  letI := manifold_realSmooth M
  apply contDiff_pi.mpr
  intro idx
  rw [contDiff_iff_contDiffAt]
  intro v₀
  let c := unitaryExponential g p U v₀
  have hc : unitaryExponential g p U v₀ ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hz : chartPt c c ∈ chartTarget c := mem_extChartAt_target c
  have hq := unitaryExponential_chart_smoothAt g p U c v₀ hc
  have hP := radialFrameCoordinates_smoothAt g p U c v₀ hc
  have H : ContDiffAt ℝ ∞
      (fun v => tensorEvaluation (rmJet g.form c m (chartPt c (unitaryExponential g p U v)))
        (fun j => realCoord (radialFrameCoordinates g p U c v (realVec (idx j))))) v₀ := by
    unfold tensorEvaluation tensorProduct
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.mul
    · exact ((rmJet_contDiffOn g.form (metricSmooth_of_smoothMetric g) c m a).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).comp v₀ hq
    · apply contDiffAt_prod
      intro j _
      simpa only [Function.comp_def, realCoordCLM_apply] using
        (realCoordCLM (a j)).contDiff.contDiffAt.comp v₀
          (hP.clm_apply (contDiffAt_const (c := realVec (idx j))))
  apply H.congr_of_eventuallyEq
  filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with v hv
  exact radialCurvatureCoefficients_in_chart g p U m c v hv idx

end Yau.Proofs.C04ChartsAux
