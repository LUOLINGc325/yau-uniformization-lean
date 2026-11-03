import Yau.Proofs.C04BoundedGeometryChartsFrameCurvature
import Yau.Proofs.C04BoundedGeometryChartsRadialConnection
import Yau.Proofs.C04BoundedGeometryChartsCurvatureForms
import Yau.Proofs.C04BoundedGeometryChartsRadialTorsion

/-! The curvature of the actual radial connection is the actual original curvature. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix InnerProductSpace
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem radialConnection_curvature_in_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v u w z : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    radialFrameCoordinates g p U c v (connectionCurvature (radialConnection g p U) v u w z) =
      connectionCurvature (chartChristoffelBilin g.form c) (chartPt c (unitaryExponential g p U v))
        (fderiv ℝ (fun x => chartPt c (unitaryExponential g p U x)) v u)
        (fderiv ℝ (fun x => chartPt c (unitaryExponential g p U x)) v w)
        (radialFrameCoordinates g p U c v z) := by
  letI := manifold_realSmooth M
  have heq : radialConnection g p U =ᶠ[𝓝 v] radialConnectionInChart g p U c := by
    filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with x hx
    exact radialConnection_eq_in_chart g p U c x hx
  have hcurv : connectionCurvature (radialConnection g p U) v u w z =
      connectionCurvature (radialConnectionInChart g p U c) v u w z := by
    simp only [connectionCurvature, heq.fderiv_eq, heq.self_of_nhds]
  rw [hcurv]
  have hz : chartPt c (unitaryExponential g p U v) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  exact coordinateFrameConnection_curvature (chartChristoffelBilin g.form c)
    (fun x => chartPt c (unitaryExponential g p U x)) (radialFrameCoordinates g p U c) v u w z
    ((chartChristoffelBilin_contDiffOn g c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz))
    (unitaryExponential_chart_smoothAt g p U c v hc)
    (radialFrameCoordinates_smoothAt g p U c v hc) (radialFrameCoordinates_invertible g p U c v hc)

theorem radialConnection_curvature_pairing (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j)
    (v u w z a : ComplexVector n) :
    2 * (⟪a, connectionCurvature (radialConnection g p U) v u w z⟫_ℂ).re =
      radialCurvatureForm g p U 0 v ![radialCoframe g p U v u, radialCoframe g p U v w, z, a] := by
  let c := unitaryExponential g p U v
  let Z := fun x => chartPt c (unitaryExponential g p U x)
  let P := radialFrameCoordinates g p U c
  let A := radialCoframe g p U
  let F := connectionCurvature (radialConnection g p U) v u w z
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hPA (b : ComplexVector n) : P v (A v b) = fderiv ℝ Z v b :=
    congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L b)
      (radialFrameCoordinates_comp_coframe g p U c v hc)
  have H := (realMetricInChart_tangentCoords g.form c c (mem_chart_source _ _)
    (radialParallelFrame g p U v a) (radialParallelFrame g p U v F)).trans
      (radialParallelFrame_metric g p U hU v a F)
  change realMetricInChart g.form c (Z v) (P v a) (P v F) = _ at H
  rw [radialConnection_curvature_in_chart g p U c v u w z hc, realMetricInChart_symm] at H
  rw [Yau.NodeProofs.P02Aux.connectionCurvature_pair_eq_coordinateRm g.form
    (metricSmooth_of_smoothMetric g) c (z := Z v) (mem_extChartAt_target c),
    Yau.NodeProofs.P02Aux.coordinateRm_eq_tensorEval] at H
  have HR : radialCurvatureForm g p U 0 v ![A v u, A v w, z, a] =
      tensorEvalCLM (rmTensor g.form c (Z v)) ![fderiv ℝ Z v u, fderiv ℝ Z v w, P v z, P v a] := by
    rw [radialCurvatureForm_in_chart g p U 0 c v hc,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i
    · exact hPA u
    · exact hPA w
    · rfl
    · rfl
  exact H.symm.trans HR.symm

end Yau.Proofs.C04ChartsAux
