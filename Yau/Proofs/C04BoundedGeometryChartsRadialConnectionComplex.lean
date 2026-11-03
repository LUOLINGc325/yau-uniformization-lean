import Yau.Proofs.C04BoundedGeometryChartsNormalComplexStructure

/-! The genuine Kähler radial connection commutes with multiplication by i. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L21Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem radialFrameCoordinates_complex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier)
    (v w : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    radialFrameCoordinates g p U c v (Complex.I • w) =
      Complex.I • radialFrameCoordinates g p U c v w := by
  change realTangentCoords c (unitaryExponential g p U v)
      (radialParallelFrame g p U v (Complex.I • w)) = _
  rw [radialParallelFrame_intertwines g hk, realTangentJ_eq_accepted,
    Yau.NodeProofs.P02Aux.realTangentCoords_realTangentJ c _ hc]
  rfl

theorem radialFrameCoordinates_fderiv_complex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (c : M.Carrier)
    (v u w : ComplexVector n)
    (hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source) :
    fderiv ℝ (radialFrameCoordinates g p U c) v u (Complex.I • w) =
      Complex.I • fderiv ℝ (radialFrameCoordinates g p U c) v u w := by
  have hP := (radialFrameCoordinates_smoothAt g p U c v hc).differentiableAt (by simp)
  have h₁ := hP.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • w) v)
  have h₂ := (stdComplex n).hasFDerivAt.comp v
    (hP.hasFDerivAt.clm_apply (hasFDerivAt_const w v))
  have heq : (fun y => radialFrameCoordinates g p U c y (Complex.I • w)) =ᶠ[𝓝 v]
      (fun y => stdComplex n (radialFrameCoordinates g p U c y w)) := by
    filter_upwards [(unitaryExponential_smooth g p U).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (ComplexVector n) c).open_source.mem_nhds hc)] with y hy
    exact radialFrameCoordinates_complex g hk p U c y w hy
  have H := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u)
    (h₂.unique (h₁.congr_of_eventuallyEq heq.symm))
  simpa only [ContinuousLinearMap.comp_apply, add_apply, zero_apply,
    ContinuousLinearMap.flip_apply, map_zero, zero_add, stdComplex_apply] using H.symm

theorem radialConnection_complex (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v u w : ComplexVector n) :
    radialConnection g p U v u (Complex.I • w) =
      Complex.I • radialConnection g p U v u w := by
  let c := unitaryExponential g p U v
  have hc : unitaryExponential g p U v ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hi := radialFrameCoordinates_invertible g p U c v hc
  have hz : chartPt c (unitaryExponential g p U v) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source (by simpa only [extChartAt_source] using hc)
  apply hi.injective
  rw [radialFrameCoordinates_complex g hk p U c v _ hc,
    radialConnection_eq_in_chart g p U c v hc]
  change radialFrameCoordinates g p U c v
      (coordinateFrameConnection _ _ _ v u (Complex.I • w)) =
    Complex.I • radialFrameCoordinates g p U c v (coordinateFrameConnection _ _ _ v u w)
  rw [coordinateFrameConnection_equation _ _ _ v u (Complex.I • w) hi,
    coordinateFrameConnection_equation _ _ _ v u w hi,
    radialFrameCoordinates_fderiv_complex g hk p U c v u w hc,
    radialFrameCoordinates_complex g hk p U c v w hc,
    Yau.NodeProofs.P02Aux.chartChristoffelBilin_I_right g.form (metricSmooth_of_smoothMetric g) hk c hz]
  exact (smul_add _ _ _).symm

end Yau.Proofs.C04ChartsAux
