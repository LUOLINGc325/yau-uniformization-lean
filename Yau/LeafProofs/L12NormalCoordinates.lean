import Yau.LeafProofs.L12GeodesicVariation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine exponential in the original base chart and its initial
coordinate tangent frame. -/
def realExponentialCoordinates (g : SmoothMetric M) (x : M.Carrier)
    (v : ComplexVector n) : ComplexVector n :=
  chartPt x (realExponentialMap g x (realFrameCLM x x v))

set_option backward.isDefEq.respectTransparency false in
theorem realExponentialCoordinates_contDiffAt_zero (g : SmoothMetric M) (x : M.Carrier) :
    ContDiffAt ℝ 1 (realExponentialCoordinates g x) 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  have hExp := (realExponentialMap_contMDiff g x).contMDiffAt
    (x := realFrameCLM x x (0 : ComplexVector n))
  have hframe : ContMDiffAt 𝓘(ℝ, ComplexVector n)
      𝓘(ℝ, TangentSpace 𝓘(ℝ, ComplexVector n) x) 1 (realFrameCLM x x) 0 :=
    (realFrameCLM x x).contMDiff.contMDiffAt
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartPt x) (realExponentialMap g x (realFrameCLM x x (0 : ComplexVector n))) := by
    simp only [map_zero, realExponentialMap_zero]
    exact contMDiffAt_extChartAt (I := 𝓘(ℝ, ComplexVector n))
  exact (hchart.comp 0 (hExp.comp 0 hframe)).contDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem realExponentialCoordinates_radial_hasDerivAt_zero (g : SmoothMetric M)
    (x : M.Carrier) (v : ComplexVector n) :
    HasDerivAt (fun t : ℝ => realExponentialCoordinates g x (t • v)) v 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, realFrameCLM x x v⟩
  have hη := (realGeodesic_chart_eventually g (realGeodesicFlow g p)
    ((realGeodesicFlow_integral g p).isMIntegralCurveAt 0)).self_of_nhds
  rw [realGeodesicFlow_zero] at hη
  have hd : HasDerivAt
      (fun t => (extChartAt (realPhaseModel n) p (realGeodesicFlow g p t)).1)
      (chartGeodesicSpray g.form p.proj (extChartAt (realPhaseModel n) p p)).1 0 :=
    (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt
      0 hη.2
  have hvel : (chartGeodesicSpray g.form p.proj
      (extChartAt (realPhaseModel n) p p)).1 = v := by
    change (extChartAt (realPhaseModel n) p p).2 = v
    rw [realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)]
    exact realTangentCoords_realFrameCLM x x (mem_chart_source _ _) v
  rw [hvel] at hd
  have heq : (fun t => (extChartAt (realPhaseModel n) p (realGeodesicFlow g p t)).1)
      =ᶠ[𝓝 0] (fun t => chartPt x (realGeodesicFlow g p t).proj) := by
    have hcont := (realGeodesicFlow_contMDiff g p).continuous.continuousAt (x := 0)
    have hn := hcont.preimage_mem_nhds
      (by rw [realGeodesicFlow_zero]; exact extChartAt_source_mem_nhds (I := realPhaseModel n) p)
    filter_upwards [hn] with t ht
    rw [realPhaseChart_eq_extChartAt p _ ((realPhaseChart_source p _).mp ht)]
    rfl
  have hbase := heq.hasDerivAt_iff.mp hd
  have hrad : (fun t : ℝ => realExponentialCoordinates g x (t • v)) =
      (fun t => chartPt x (realGeodesicFlow g p t).proj) := by
    funext t
    simp only [realExponentialCoordinates, map_smul, realExponentialMap_smul, p]
  rwa [hrad]

/-- The differential at zero of the actual exponential in genuine tangent
and base coordinates is the identity. -/
theorem hasFDerivAt_realExponentialCoordinates_zero (g : SmoothMetric M) (x : M.Carrier) :
    HasFDerivAt (realExponentialCoordinates g x)
      (ContinuousLinearMap.id ℝ (ComplexVector n)) 0 := by
  have hd := (realExponentialCoordinates_contDiffAt_zero g x).differentiableAt (by simp)
  have hD : fderiv ℝ (realExponentialCoordinates g x) 0 =
      ContinuousLinearMap.id ℝ (ComplexVector n) := by
    apply ContinuousLinearMap.ext
    intro v
    have hin : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
    have hout : HasDerivAt (fun t : ℝ => realExponentialCoordinates g x (t • v))
        (fderiv ℝ (realExponentialCoordinates g x) 0 v) 0 := by
      have hDAt : HasFDerivAt (realExponentialCoordinates g x)
          (fderiv ℝ (realExponentialCoordinates g x) 0) ((0 : ℝ) • v) := by
        simpa only [zero_smul] using hd.hasFDerivAt
      exact hDAt.comp_hasDerivAt 0 hin
    exact hout.unique (realExponentialCoordinates_radial_hasDerivAt_zero g x v)
  rw [← hD]
  exact hd.hasFDerivAt

/-- The actual exponential with initial vector in the genuine chart frame. -/
def realNormalExponentialMap (g : SmoothMetric M) (x : M.Carrier)
    (v : ComplexVector n) : M.Carrier :=
  realExponentialMap g x (realFrameCLM x x v)

theorem realNormalExponentialMap_zero (g : SmoothMetric M) (x : M.Carrier) :
    realNormalExponentialMap g x 0 = x := by
  simp only [realNormalExponentialMap, map_zero, realExponentialMap_zero]

theorem realNormalExponentialMap_contMDiff (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (realNormalExponentialMap g x) := by
  letI := manifold_realSmooth M
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  letI := underlyingRealTangentInnerProductSpace g.form x
  exact (realExponentialMap_contMDiff g x).comp
    (realFrameCLM x x).contMDiff

set_option backward.isDefEq.respectTransparency false in
/-- A genuine normal-coordinate neighborhood from the actual exponential,
including C1 regularity of the inverse at the center. -/
theorem exists_realExponential_normalCoordinates (g : SmoothMetric M) (x : M.Carrier) :
    letI := manifold_realSmooth M
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      (0 : ComplexVector n) ∈ e.source ∧ e 0 = x ∧
      Set.EqOn e (realNormalExponentialMap g x) e.source ∧
      ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e e.source ∧
      ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e.symm x := by
  letI := manifold_realSmooth M
  let F := realExponentialCoordinates g x
  have hF := realExponentialCoordinates_contDiffAt_zero g x
  have hD : HasFDerivAt F
      ((ContinuousLinearEquiv.refl ℝ (ComplexVector n)) :
        ComplexVector n →L[ℝ] ComplexVector n) 0 :=
    hasFDerivAt_realExponentialCoordinates_zero g x
  let c := hF.toOpenPartialHomeomorph F hD (by simp)
  have h0c : (0 : ComplexVector n) ∈ c.source :=
    hF.mem_toOpenPartialHomeomorph_source hD (by simp)
  let U := realNormalExponentialMap g x ⁻¹' (chartAt (ComplexVector n) x).source
  have hU : IsOpen U := (chartAt (ComplexVector n) x).open_source.preimage
    (realNormalExponentialMap_contMDiff g x).continuous
  have h0U : (0 : ComplexVector n) ∈ U := by
    change realNormalExponentialMap g x 0 ∈ (chartAt (ComplexVector n) x).source
    rw [realNormalExponentialMap_zero]
    exact mem_chart_source _ _
  let e := (c.restr U).trans (chartAt (ComplexVector n) x).symm
  have h0e : (0 : ComplexVector n) ∈ e.source := by
    rw [OpenPartialHomeomorph.trans_source, c.restr_source' U hU]
    refine ⟨⟨h0c, h0U⟩, ?_⟩
    change chartPt x (realNormalExponentialMap g x 0) ∈ (chartAt (ComplexVector n) x).target
    rw [realNormalExponentialMap_zero]
    exact (chartAt (ComplexVector n) x).map_source (mem_chart_source _ _)
  have heq : Set.EqOn e (realNormalExponentialMap g x) e.source := by
    intro v hv
    have hv' : v ∈ c.source ∩ U := by
      have h : v ∈ (c.restr U).source := hv.1
      rwa [c.restr_source' U hU] at h
    change (chartAt (ComplexVector n) x).symm
      ((chartAt (ComplexVector n) x) (realNormalExponentialMap g x v)) = _
    exact (chartAt (ComplexVector n) x).left_inv hv'.2
  have hC : ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 e e.source :=
    (contMDiffOn_congr heq).mpr (realNormalExponentialMap_contMDiff g x).contMDiffOn
  have hInv : ContDiffAt ℝ 1 c.symm (chartPt x x) := by
    have h := hF.to_localInverse hD (by simp)
    change ContDiffAt ℝ 1 c.symm (F 0) at h
    simpa only [F, realExponentialCoordinates, map_zero, realExponentialMap_zero] using h
  have hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
      (chartAt (ComplexVector n) x) x := contMDiffAt_extChartAt
  have hInvM := hInv.contMDiffAt.comp x hchart
  refine ⟨e, h0e, (heq h0e).trans (realNormalExponentialMap_zero g x), heq, hC, ?_⟩
  exact hInvM

end Yau.LeafProofs.L12Aux
