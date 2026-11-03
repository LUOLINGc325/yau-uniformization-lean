import Yau.LeafProofs.L12EndpointEnergy

/-! Smooth actual phase coordinates in an arbitrary fixed base chart. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-- Genuine phase coordinates are smooth wherever the underlying base
chart is defined. -/
theorem realPhaseChart_contMDiffAt (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hy : q.proj ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (realPhaseChart y) q := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let r : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨y, 0⟩
  let C := extChartAt (realPhaseModel n) r
  have hs : q ∈ C.source := (realPhaseChart_source r q).mpr hy
  have hC : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞ C q :=
    contMDiffAt_extChartAt' (by simpa only [C, extChartAt_source] using hs)
  apply hC.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := realPhaseModel n) r).mem_nhds hs] with p hp
  exact (realPhaseChart_eq_extChartAt r p ((realPhaseChart_source r p).mp hp)).symm

/-- The velocity component of a genuine tangent-bundle phase chart. -/
def realChartVelocity (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) : ComplexVector n :=
  realTangentCoords y q.proj q.2

theorem realChartVelocity_contMDiffAt (y : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (hy : q.proj ∈ (chartAt (ComplexVector n) y).source) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) ∞ (realChartVelocity y) q := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact ((contDiff_snd (𝕜 := ℝ) (E := ComplexVector n) (F := ComplexVector n)).contMDiff
    (realPhaseChart y q)).comp q (realPhaseChart_contMDiffAt y q hy)

/-- Actual physical positive definiteness in centered real coordinates. -/
theorem realMetricInChart_self_pos (g : SmoothMetric M) (y : M.Carrier)
    {v : ComplexVector n} (hv : v ≠ 0) :
    0 < realMetricInChart g.form y (chartPt y y) v v := by
  letI := underlyingRealTangentNormedAddCommGroup g.form y
  letI := underlyingRealTangentInnerProductSpace g.form y
  rw [realMetricInChart_self_frame]
  change 0 < ⟪realFrameCLM y y v, realFrameCLM y y v⟫_ℝ
  rw [real_inner_self_eq_norm_sq]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hh
  apply hv
  have hc := congrArg (realTangentCoords y y) hh
  rw [realTangentCoords_realFrameCLM y y (mem_chart_source _ _), map_zero] at hc
  exact hc

/-- The differential of actual chart velocity is the second component of
the differential of the actual phase chart. -/
theorem realChartVelocity_comp_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (z : E) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiffAt 𝓘(ℝ, E) (realPhaseModel n) 1 F z →
    fderiv ℝ (fun u => realChartVelocity (F z).proj (F u)) z =
      (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).comp
        (fderiv ℝ (fun u => extChartAt (realPhaseModel n) (F z) (F u)) z) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hF
  let C := extChartAt (realPhaseModel n) (F z)
  have hC : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) 1 C (F z) :=
    contMDiffAt_extChartAt
  have hCF := (hC.comp z hF).contDiffAt.differentiableAt (by simp)
  have hproj := (ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp z hCF.hasFDerivAt
  have heq : (fun u => realChartVelocity (F z).proj (F u)) =ᶠ[𝓝 z]
      (fun u => (C (F u)).2) := by
    filter_upwards [hF.continuousAt.eventually
      (extChartAt_source_mem_nhds (I := realPhaseModel n) (F z))] with u hu
    have h := realPhaseChart_eq_extChartAt (F z) (F u) ((realPhaseChart_source (F z) (F u)).mp hu)
    change (realPhaseChart (F z).proj (F u)).2 = (C (F u)).2
    rw [h]
  exact (heq.hasFDerivAt_iff.mpr hproj).fderiv

end Yau.LeafProofs.L12Aux
