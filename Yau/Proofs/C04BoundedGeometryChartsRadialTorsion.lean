import Yau.Proofs.C04BoundedGeometryChartsRadialConnection
import Yau.Proofs.C04BoundedGeometryChartsRadialPullback
import Yau.Proofs.C04BoundedGeometryChartsFrameTorsion

/-! The actual exponential coframe and actual radial connection satisfy the torsion equation. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem radialFrameCoordinates_comp_coframe (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier) (v : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    (radialFrameCoordinates g p U c v).comp (radialCoframe g p U v) =
      fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) v := by
  apply ContinuousLinearMap.ext
  intro w
  change realTangentCoords c (unitaryExponential g p U v)
    (radialParallelFrame g p U v (radialCoframe g p U v w)) = _
  rw [radialParallelFrame_radialCoframe]
  exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
    (realMapDeriv_coordinates g p U c v hc)

theorem radialCoframe_torsion (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v u w : ComplexVector n) :
    fderiv ℝ (radialCoframe g p U) v u w - fderiv ℝ (radialCoframe g p U) v w u +
      radialConnection g p U v u (radialCoframe g p U v w) -
        radialConnection g p U v w (radialCoframe g p U v u) = 0 := by
  letI := manifold_realSmooth M
  let c := unitaryExponential g p U v
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hPA : (fun z => (radialFrameCoordinates g p U c z).comp (radialCoframe g p U z)) =ᶠ[𝓝 v]
      fderiv ℝ (fun w => chartPt c (unitaryExponential g p U w)) := by
    filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with z hz
    exact radialFrameCoordinates_comp_coframe g p U c z hz
  exact coordinateFrameConnection_torsion (chartChristoffelBilin g.form c)
    (fun w => chartPt c (unitaryExponential g p U w)) (radialFrameCoordinates g p U c)
    (radialCoframe g p U) v u w
    ((unitaryExponential_chart_smoothAt g p U c v hc).of_le (by simp))
    ((radialFrameCoordinates_smoothAt g p U c v hc).differentiableAt (by simp))
    ((radialCoframe_smooth g p U).differentiable (by simp) v)
    (radialFrameCoordinates_invertible g p U c v hc) hPA
    (chartChristoffelBilin_symm g.form c _)

end Yau.Proofs.C04ChartsAux
