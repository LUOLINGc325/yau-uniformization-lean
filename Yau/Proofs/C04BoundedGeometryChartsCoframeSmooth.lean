import Yau.Proofs.C04BoundedGeometryChartsFrameCoordinates

/-! Smoothness of the actual exponential coframe on its entire parameter space. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem unitaryExponential_chart_smoothAt (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    ContDiffAt ℝ ∞ (fun w => chartPt c (unitaryExponential g p U w)) v := by
  letI := manifold_realSmooth M
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) ∞
      (chartPt c) (unitaryExponential g p U v) :=
    contMDiffAt_extChartAt' hc
  exact (hchart.comp v (unitaryExponential_smooth g p U).contMDiffAt).contDiffAt

theorem realMapDeriv_coordinates (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    (realTangentCoords c (unitaryExponential g p U v)).comp
      (realMapDeriv (unitaryExponential g p U) v) =
        fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) v := by
  letI := manifold_realSmooth M
  apply ContinuousLinearMap.ext
  intro w
  exact realTangentCoords_mfderiv (unitaryExponential g p U) v c hc w
    ((unitaryExponential_smooth g p U).mdifferentiableAt (by simp))

theorem radialCoframe_eq_coordinate_formula (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    radialCoframe g p U v = (radialFrameCoordinates g p U c v).inverse.comp
      (fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) v) := by
  apply ContinuousLinearMap.ext
  intro w
  have hi := radialFrameCoordinates_invertible g p U c v hc
  apply hi.injective
  rw [ContinuousLinearMap.comp_apply, hi.self_apply_inverse]
  change realTangentCoords c (unitaryExponential g p U v)
      ((radialParallelFrame g p U v) ((radialParallelFrame g p U v).symm
        (realMapDeriv (unitaryExponential g p U) v w))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
    (realMapDeriv_coordinates g p U c v hc)

theorem radialCoframe_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    ContDiff ℝ ∞ (radialCoframe g p U) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro v₀
  let c := unitaryExponential g p U v₀
  have hc : unitaryExponential g p U v₀ ∈ (chartAt (ComplexVector n) c).source :=
    mem_chart_source _ _
  have hP := radialFrameCoordinates_smoothAt g p U c v₀ hc
  have hPi : ContDiffAt ℝ ∞ (fun v => (radialFrameCoordinates g p U c v).inverse) v₀ :=
    (radialFrameCoordinates_invertible g p U c v₀ hc).contDiffAt_map_inverse.comp v₀ hP
  have hD := (unitaryExponential_chart_smoothAt g p U c v₀ hc).fderiv_right
    (m := ∞) (by simp)
  apply (hPi.clm_comp hD).congr_of_eventuallyEq
  filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with v hv
  exact radialCoframe_eq_coordinate_formula g p U c v hv

end Yau.Proofs.C04ChartsAux
