import Yau.Proofs.C04BoundedGeometryChartsParallelFrameFlow
import Yau.Proofs.C04BoundedGeometryChartsTransportRegularity

/-! Smooth dependence of the actual parallel frame on its radial parameter. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Bundle

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realTransportFiber_smooth (g : SmoothMetric M) (p : M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realTransport M
    letI := underlyingRealTangentNormedAddCommGroup g.form p
    letI := underlyingRealTangentInnerProductSpace g.form p
    ContMDiff 𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p ×
      TangentSpace 𝓘(ℝ, ComplexVector n) p) (realTransportModel n) ∞
      (fun w => (⟨p, w⟩ : realTransportBundle M)) := by
  letI := manifold_realSmooth M
  letI := manifold_realTransport M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  intro v
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_const, ?_⟩
  let b := trivializationAt (ComplexVector n × ComplexVector n)
    ((fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) ×ᵇ
      (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x)) p
  have heq : (fun w : TangentSpace 𝓘(ℝ, ComplexVector n) p ×
      TangentSpace 𝓘(ℝ, ComplexVector n) p => (b (⟨p, w⟩ : realTransportBundle M)).2) =
      b.continuousLinearMapAt ℝ p := by
    funext w
    exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _
      (mem_baseSet_trivializationAt (ComplexVector n × ComplexVector n)
        ((fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x) ×ᵇ
          (fun x : M.Carrier => TangentSpace 𝓘(ℝ, ComplexVector n) x)) p) w).symm
  rw [heq]
  exact (b.continuousLinearMapAt ℝ p).contMDiff.contMDiffAt

theorem radialParallelLift_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff 𝓘(ℝ, ComplexVector n) (realPhaseModel n) ∞
      (fun v => realParallelLift g (radialInitialState p U v) w 1) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := manifold_realTransport M
  letI := underlyingRealTangentNormedAddCommGroup g.form p
  letI := underlyingRealTangentInnerProductSpace g.form p
  have hin : ContMDiff 𝓘(ℝ, ComplexVector n)
      𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) p ×
        TangentSpace 𝓘(ℝ, ComplexVector n) p) ∞
      (fun v => (realUnitaryFrame p U v, w)) :=
    (realUnitaryFrame p U).toContinuousLinearMap.contMDiff.prodMk_space
    (contMDiff_const (c := w))
  have hinput := (realTransportFiber_smooth g p).comp hin
  have hflow := (realParallelTransportFlow_joint_smooth g).comp
    (hinput.prodMk (contMDiff_const (c := (1 : ℝ))))
  exact realTransportVector_contMDiff.comp hflow

theorem radialParallelCoordinates_smoothAt (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p) (c : M.Carrier) (v₀ : ComplexVector n)
    (hc : unitaryExponential g p U v₀ ∈ (chartAt (ComplexVector n) c).source) :
    ContDiffAt ℝ ∞ (fun v => realTangentCoords c (unitaryExponential g p U v)
      (realParallelField g (radialInitialState p U v) w 1)) v₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let B := fun v => realParallelLift g (radialInitialState p U v) w 1
  let pc : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨c, 0⟩
  have hB : ContMDiff 𝓘(ℝ, ComplexVector n) (realPhaseModel n) ∞ B :=
    radialParallelLift_smooth g p U w
  have htotal (v : ComplexVector n) :
      (⟨unitaryExponential g p U v, realParallelField g (radialInitialState p U v) w 1⟩ :
        TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) = B v := by
    simpa only [unitaryExponential, realExponentialMap, radialInitialState, B] using
      realParallelField_totalSpace g (radialInitialState p U v) w 1
  have hb₀ : B v₀ ∈ (extChartAt (realPhaseModel n) pc).source := by
    apply (realPhaseChart_source pc (B v₀)).mpr
    rw [← htotal]
    exact hc
  have hchart : ContMDiffAt (realPhaseModel n)
      𝓘(ℝ, ComplexVector n × ComplexVector n) ∞ (extChartAt (realPhaseModel n) pc) (B v₀) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hb₀)
  have hcoords : ContDiffAt ℝ ∞ (fun v => (extChartAt (realPhaseModel n) pc (B v)).2) v₀ :=
    ((hchart.comp v₀ hB.contMDiffAt).contDiffAt).snd
  have heq : (fun v => (extChartAt (realPhaseModel n) pc (B v)).2) =ᶠ[𝓝 v₀]
      (fun v => realTangentCoords c (unitaryExponential g p U v)
        (realParallelField g (radialInitialState p U v) w 1)) := by
    filter_upwards [hB.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := realPhaseModel n) pc).mem_nhds hb₀)] with v hv
    rw [realPhaseChart_eq_extChartAt pc (B v) ((realPhaseChart_source pc (B v)).mp hv)]
    change realTangentCoords c (B v).proj (B v).2 = _
    rw [← htotal]
  exact hcoords.congr_of_eventuallyEq heq.symm

end Yau.Proofs.C04ChartsAux
