import Yau.Proofs.C04BoundedGeometryChartsFrameConnectionChange

/-! The actual radial connection is independent of the target chart and is smooth. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem realTangentCoords_chart_change (c d y : M.Carrier)
    (hc : y ∈ (chartAt (ComplexVector n) c).source)
    (hd : y ∈ (chartAt (ComplexVector n) d).source) :
    (fderiv ℝ (realChartChange c d) (chartPt c y)).comp (realTangentCoords c y) =
      realTangentCoords d y := by
  have hc' : y ∈ (extChartAt (ComplexModel n) c).source := by simpa only [extChartAt_source] using hc
  have hd' : y ∈ (extChartAt (ComplexModel n) d).source := by simpa only [extChartAt_source] using hd
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hc'
  have hinv : chartInv c (chartPt c y) = y := (extChartAt (ComplexModel n) c).left_inv hc'
  have hy : chartInv c (chartPt c y) ∈ (extChartAt (ComplexModel n) d).source := by rwa [hinv]
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, realChartChange_fderiv c d hz hy, hinv,
    ← realFrameCLM_apply c y hc, realFrameCLM_realTangentCoords c y hc]

theorem radialConnectionInChart_change (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c d : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source)
    (hd : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) d).source) :
    radialConnectionInChart g p U c v = radialConnectionInChart g p U d v := by
  letI := manifold_realSmooth M
  let E := unitaryExponential g p U
  let Z := fun w => chartPt c (E w)
  let W := fun w => chartPt d (E w)
  let f := realChartChange c d
  have hE : Continuous E := (unitaryExponential_smooth g p U).continuous
  have hnear : ∀ᶠ w in 𝓝 v, E w ∈ (chartAt (ComplexVector n) c).source ∧
      E w ∈ (chartAt (ComplexVector n) d).source :=
    hE.continuousAt.preimage_mem_nhds
      (inter_mem ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)
        ((chartAt (ComplexVector n) d).open_source.mem_nhds hd))
  have hW : W =ᶠ[𝓝 v] (f ∘ Z) := by
    filter_upwards [hnear] with w hw
    have hi : chartInv c (chartPt c (E w)) = E w :=
      (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using hw.1)
    change chartPt d (E w) = chartPt d (chartInv c (chartPt c (E w)))
    rw [hi]
  have hPQ : radialFrameCoordinates g p U d =ᶠ[𝓝 v]
      (fun w => (fderiv ℝ f (Z w)).comp (radialFrameCoordinates g p U c w)) := by
    filter_upwards [hnear] with w hw
    apply ContinuousLinearMap.ext
    intro a
    exact (congrArg (fun L => L (radialParallelFrame g p U w a))
      (realTangentCoords_chart_change c d (E w) hw.1 hw.2)).symm
  have hc' : E v ∈ (extChartAt (ComplexModel n) c).source := by simpa only [extChartAt_source] using hc
  have hd' : E v ∈ (extChartAt (ComplexModel n) d).source := by simpa only [extChartAt_source] using hd
  have hz : Z v ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hc'
  have hinv : chartInv c (Z v) = E v := (extChartAt (ComplexModel n) c).left_inv hc'
  have hy : chartInv c (Z v) ∈ (extChartAt (ComplexModel n) d).source := by rwa [hinv]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro w
  exact coordinateFrameConnection_change (chartChristoffelBilin g.form c) (chartChristoffelBilin g.form d)
    Z W f (radialFrameCoordinates g p U c) (radialFrameCoordinates g p U d) v u w
    ((unitaryExponential_chart_smoothAt g p U c v hc).differentiableAt (by simp))
    ((radialFrameCoordinates_smoothAt g p U c v hc).differentiableAt (by simp))
    ((radialFrameCoordinates_smoothAt g p U d v hd).differentiableAt (by simp))
    ((realChartChange_contDiffAt c d hz hy).of_le (by simp)) hW hPQ
    (chartChristoffelBilin_change g c d hz hy)
    (radialFrameCoordinates_invertible g p U c v hc) (radialFrameCoordinates_invertible g p U d v hd)

theorem radialConnection_eq_in_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    radialConnection g p U v = radialConnectionInChart g p U c v :=
  radialConnectionInChart_change g p U (unitaryExponential g p U v) c v (mem_chart_source _ _) hc

theorem radialConnection_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) : ContDiff ℝ ∞ (radialConnection g p U) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro v
  let c := unitaryExponential g p U v
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  apply (radialConnectionInChart_smoothAt g p U c v hc).congr_of_eventuallyEq
  filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with w hw
  exact radialConnection_eq_in_chart g p U c w hw

end Yau.Proofs.C04ChartsAux
