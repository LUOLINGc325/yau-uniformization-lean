import Yau.LeafProofs.L12EndpointBranch

/-! Actual inverse-time phase differentials and genuine Jacobi kernel data. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

theorem realGeodesicPhaseFlow_contMDiff (g : SmoothMetric M) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) (realPhaseModel n) 1
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => realGeodesicFlow g q t) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact (realGeodesicFlow_joint_contMDiff g).comp (contMDiff_id.prodMk (contMDiff_const (c := t)))

/-- The actual fixed-time phase flow, read in the genuine source and
endpoint phase charts. -/
def realGeodesicPhaseChartMap (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    ComplexVector n × ComplexVector n → ComplexVector n × ComplexVector n := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  exact extChartAt (realPhaseModel n) (realGeodesicFlow g p t) ∘
    (fun q => realGeodesicFlow g q t) ∘ (extChartAt (realPhaseModel n) p).symm

theorem realGeodesicPhaseChartMap_contDiffAt (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContDiffAt ℝ 1 (realGeodesicPhaseChartMap g p t) (extChartAt (realPhaseModel n) p p) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  have h := (contMDiffAt_iff.mp (realGeodesicPhaseFlow_contMDiff g t p)).2
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h

/-- The actual full phase differential in initial velocity is injective,
by differentiating the actual inverse-time phase flow. -/
theorem realVelocityPhaseCoordinates_fderiv_injective (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    Function.Injective (fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  let U := realVelocityPhaseCoordinates g p t
  let V := realVelocityPhaseCoordinates g p 0
  let p₁ := realGeodesicFlow g p t
  let H := realGeodesicPhaseChartMap g p₁ (-t)
  have hInv (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
      realGeodesicFlow g (realGeodesicFlow g q t) (-t) = q := by
    rw [← realGeodesicFlow_add, add_neg_cancel, realGeodesicFlow_zero]
  have hH := (realGeodesicPhaseChartMap_contDiffAt g p₁ (-t)).differentiableAt (by simp)
  have hU := (realVelocityPhaseCoordinates_contDiffAt g p t).differentiableAt (by simp)
  have hV := (realVelocityPhaseCoordinates_contDiffAt g p 0).differentiableAt (by simp)
  have hcomp := hH.hasFDerivAt.comp p.2 hU.hasFDerivAt
  have hN : ∀ᶠ a : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj in 𝓝 p.2,
      realGeodesicFlow g (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) t ∈
        (extChartAt (realPhaseModel n) p₁).source :=
    (realVelocityFlow_contMDiff g p.proj t).continuous.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realPhaseModel n) p₁)
  have heq : H ∘ U =ᶠ[𝓝 p.2] V := by
    filter_upwards [hN] with a ha
    dsimp only [H, realGeodesicPhaseChartMap, Function.comp_apply, U, V, realVelocityPhaseCoordinates]
    rw [hInv p, (extChartAt (realPhaseModel n) p₁).left_inv ha,
      hInv (⟨p.proj, a⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier),
      realGeodesicFlow_zero, realGeodesicFlow_zero]
  have hD := (heq.hasFDerivAt_iff.mp hcomp).unique hV.hasFDerivAt
  intro a b hab
  have hz : fderiv ℝ U p.2 (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj →L[ℝ]
    ComplexVector n × ComplexVector n => L (a - b)) hD
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [hz, map_zero, realVelocityPhaseCoordinates_zero_fderiv_apply] at h
  have hc := congrArg Prod.snd h
  change 0 = realTangentCoords p.proj p.proj (a - b) at hc
  have hw := congrArg (realFrameCLM p.proj p.proj) hc
  rw [map_zero, realFrameCLM_realTangentCoords p.proj p.proj (mem_chart_source _ _)] at hw
  exact sub_eq_zero.mp hw.symm

/-- A nontrivial actual Jacobi field which vanishes at a time has a
nonzero velocity-variation component there. -/
theorem realVelocityPhaseCoordinates_snd_ne_zero_of_Jacobi_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj) (hw : w ≠ 0)
    (hJ : realGeodesicJacobiField g p w t = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    (fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2 w).2 ≠ 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
  letI := underlyingRealTangentInnerProductSpace g.form p.proj
  have hcoords := realGeodesicJacobiField_coords_of_phase_deriv g p (realGeodesicFlow g p t) t
    (fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2) w (mem_extChartAt_source _) ((realVelocityPhaseCoordinates_contDiffAt g p t).differentiableAt (by simp)).hasFDerivAt
  rw [hJ, map_zero] at hcoords
  intro hsnd
  have hz : fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2 w = 0 :=
    Prod.ext hcoords.symm hsnd
  apply hw
  apply realVelocityPhaseCoordinates_fderiv_injective g p t
  rw [hz, map_zero]

/-- An actual singular Jacobi matrix supplies a nonzero genuine initial
variation with zero positional Jacobi value and nonzero velocity variation. -/
theorem exists_realJacobi_kernel_of_det_eq_zero (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ)
    (hdet : (realGeodesicJacobiMatrix g p t).det = 0) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    letI := underlyingRealTangentInnerProductSpace g.form p.proj
    ∃ w : TangentSpace 𝓘(ℝ, ComplexVector n) p.proj, w ≠ 0 ∧
      realGeodesicJacobiField g p w t = 0 ∧
      (fderiv ℝ (realVelocityPhaseCoordinates g p t) p.2 w).2 ≠ 0 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let b₀ := realInitialOrthonormalFrame g p.proj
  let w := b₀.repr.symm (WithLp.toLp 2 c)
  have hw : w ≠ 0 := by
    intro hw
    apply hc
    funext i
    have h := congrArg (fun v => b₀.repr v i) hw
    simpa [w] using h
  have hJ : realGeodesicJacobiField g p w t = 0 := by
    apply (realGlobalParallelFrame g p t).repr.injective
    apply PiLp.ext
    intro i
    simp only [map_zero]
    rw [realGeodesicJacobiField_coefficients g p t w]
    simpa [w, b₀] using congrFun hAc i
  exact ⟨w, hw, hJ, realVelocityPhaseCoordinates_snd_ne_zero_of_Jacobi_zero g p t w hw hJ⟩

end Yau.LeafProofs.L12Aux
