import Yau.LeafProofs.L12Flow

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def realPhaseScale (c : ℝ) (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨q.proj, c • q.2⟩

def phaseScaleCLM (n : ℕ) (c : ℝ) :
    (ComplexVector n × ComplexVector n) →L[ℝ] (ComplexVector n × ComplexVector n) :=
  (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).prod
    (c • ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n))

theorem phaseScaleCLM_apply (c : ℝ) (q : ComplexVector n × ComplexVector n) :
    phaseScaleCLM n c q = (q.1, c • q.2) := rfl

theorem realPhaseChart_realPhaseScale (c : ℝ) (x : M.Carrier)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    realPhaseChart x (realPhaseScale c q) = phaseScaleCLM n c (realPhaseChart x q) := by
  apply Prod.ext
  · rfl
  · exact (realTangentCoords x q.proj).map_smul c q.2

theorem realPhaseScale_realPhasePoint (c : ℝ) (x : M.Carrier)
    (q : ComplexVector n × ComplexVector n) :
    realPhaseScale c (realPhasePoint x q) = realPhasePoint x (phaseScaleCLM n c q) := by
  change (⟨chartInv x q.1, c • realFrameCLM x (chartInv x q.1) q.2⟩ :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) =
      ⟨chartInv x q.1, realFrameCLM x (chartInv x q.1) (c • q.2)⟩
  exact congrArg (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) (chartInv x q.1) =>
    (⟨chartInv x q.1, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier))
    ((realFrameCLM x (chartInv x q.1)).map_smul c q.2).symm

theorem realPhaseScale_eventually_eq_chart (c : ℝ)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    realPhaseScale c =ᶠ[𝓝 p]
      ((extChartAt (realPhaseModel n) p).symm ∘ phaseScaleCLM n c ∘
        extChartAt (realPhaseModel n) p) := by
  letI := manifold_realSmooth M
  filter_upwards [extChartAt_source_mem_nhds (I := realPhaseModel n) p] with q hq
  have hbase := (realPhaseChart_source p q).mp hq
  have hz : (phaseScaleCLM n c (realPhaseChart p.proj q)).1 ∈ chartTarget p.proj := by
    exact (extChartAt (ComplexModel n) p.proj).map_source
      (by simpa only [extChartAt_source] using hbase)
  change realPhaseScale c q = (extChartAt (realPhaseModel n) p).symm
    (phaseScaleCLM n c (extChartAt (realPhaseModel n) p q))
  rw [realPhaseChart_eq_extChartAt p q hbase,
    realPhasePoint_eq_extChartAt_symm p _ hz,
    ← realPhaseScale_realPhasePoint, realPhasePoint_realPhaseChart p.proj q hbase]

theorem realPhaseScale_contMDiff (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ContMDiff (realPhaseModel n) (realPhaseModel n) ∞
      (realPhaseScale (M := M) c) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  intro p
  have hz : phaseScaleCLM n c (extChartAt (realPhaseModel n) p p) ∈
      (extChartAt (realPhaseModel n) p).target := by
    apply (realPhaseChart_target p _).mpr
    rw [realPhaseChart_eq_extChartAt p p (mem_chart_source _ _)]
    exact mem_extChartAt_target p.proj
  have hi := contMDiffWithinAt_extChartAt_symm_range
    (I := realPhaseModel n) (n := ∞) p hz
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hm : ContMDiff 𝓘(ℝ, ComplexVector n × ComplexVector n)
      𝓘(ℝ, ComplexVector n × ComplexVector n) ∞ (phaseScaleCLM n c) :=
    (phaseScaleCLM n c).contDiff.contMDiff
  have hp : ContMDiffAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
      (extChartAt (realPhaseModel n) p) p := contMDiffAt_extChartAt
  exact (hi.comp p ((hm _).comp p hp)).congr_of_eventuallyEq
    (realPhaseScale_eventually_eq_chart c p)

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_realPhaseScale (c : ℝ)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    mfderiv (realPhaseModel n) (realPhaseModel n) (realPhaseScale c) p = phaseScaleCLM n c := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  have hf := (realPhaseScale_contMDiff (M := M) c p).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realPhaseModel n) (realPhaseModel n) p (realPhaseScale c)
      =ᶠ[𝓝 (extChartAt (realPhaseModel n) p p)] phaseScaleCLM n c := by
    filter_upwards [(isOpen_extChartAt_target (I := realPhaseModel n) p).mem_nhds
      (mem_extChartAt_target p)] with q hq
    have hz := (realPhaseChart_target p q).mp hq
    have hz' : (phaseScaleCLM n c q).1 ∈ chartTarget p.proj := hz
    have hsource : (realPhasePoint p.proj (phaseScaleCLM n c q)).proj ∈
        (chartAt (ComplexVector n) p.proj).source := by
      simpa only [realPhasePoint, extChartAt_source, chartInv] using
        (extChartAt (ComplexModel n) p.proj).map_target hz'
    change extChartAt (realPhaseModel n) p
      (realPhaseScale c ((extChartAt (realPhaseModel n) p).symm q)) = phaseScaleCLM n c q
    rw [realPhasePoint_eq_extChartAt_symm p q hz, realPhaseScale_realPhasePoint,
      realPhaseChart_eq_extChartAt p _ hsource]
    exact realPhaseChart_realPhasePoint p.proj _ hz'
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (phaseScaleCLM n c).hasFDerivAt.fderiv]

theorem chartGeodesicAcceleration_smul (h : HermitianField M) (x : M.Carrier)
    (z v : ComplexVector n) (c : ℝ) :
    chartGeodesicAcceleration h x z (c • v) =
      c • (c • chartGeodesicAcceleration h x z v) := by
  rw [chartGeodesicAcceleration_eq, chartGeodesicAcceleration_eq]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_neg]

theorem mfderiv_realPhaseScale_spray (g : SmoothMetric M) (c : ℝ)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    mfderiv (realPhaseModel n) (realPhaseModel n) (realPhaseScale c) q
      (c • realGeodesicSpray g q) = realGeodesicSpray g (realPhaseScale c q) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  rw [mfderiv_realPhaseScale]
  change phaseScaleCLM n c (c • chartGeodesicSpray g.form q.proj (realPhaseChart q.proj q)) =
    chartGeodesicSpray g.form q.proj (realPhaseChart q.proj (realPhaseScale c q))
  rw [realPhaseChart_realPhaseScale, phaseScaleCLM_apply, phaseScaleCLM_apply]
  apply Prod.ext
  · rfl
  · exact (chartGeodesicAcceleration_smul g.form q.proj _ _ c).symm


set_option backward.isDefEq.respectTransparency false in
theorem realGeodesic_rescale (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (c : ℝ) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurve γ (realGeodesicSpray g) →
      IsMIntegralCurve (realPhaseScale c ∘ γ ∘ (· * c)) (realGeodesicSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ t
  have hm := hγ.comp_mul c
  have hH := ((realPhaseScale_contMDiff (M := M) c (γ (t * c))).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hcomp := hH.comp t (hm t)
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change mfderiv (realPhaseModel n) (realPhaseModel n) (realPhaseScale c) (γ (t * c))
      (((1 : ℝ →L[ℝ] ℝ).smulRight (c • realGeodesicSpray g (γ (t * c)))) a) =
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (realGeodesicSpray g (realPhaseScale c (γ (t * c))))) a
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  rw [map_smul, mfderiv_realPhaseScale_spray]

theorem realGeodesicFlow_rescale (g : SmoothMetric M) (c : ℝ)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (t : ℝ) :
    realGeodesicFlow g (realPhaseScale c p) t =
      realPhaseScale c (realGeodesicFlow g p (t * c)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have h := realGeodesicFlow_unique g (realPhaseScale c p)
    (realPhaseScale c ∘ realGeodesicFlow g p ∘ (· * c))
    (by simp [realGeodesicFlow_zero])
    (realGeodesic_rescale g (realGeodesicFlow g p) c (realGeodesicFlow_integral g p))
  exact (congrFun h t).symm

theorem realExponentialMap_smul (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (c : ℝ) :
    realExponentialMap g x (c • v) =
      (realGeodesicFlow g (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) c).proj := by
  have h := realGeodesicFlow_rescale g c
    (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1
  simpa only [realExponentialMap, realPhaseScale, one_mul] using congrArg Bundle.TotalSpace.proj h

/-- Smoothness on each fixed radial line follows from the actual geodesic
ODE; this statement does not assert initial-vector differentiability. -/
theorem realExponentialMap_radial_contMDiff (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ (fun c : ℝ => realExponentialMap g x (c • v)) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞
      (fun c => (realGeodesicFlow g
        (⟨x, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) c).proj) :=
    (Bundle.contMDiff_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).comp
        (realGeodesicFlow_contMDiff g ⟨x, v⟩)
  convert h using 1
  funext c
  exact realExponentialMap_smul g x v c

theorem realExponentialMap_radial_speed (g : SmoothMetric M) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) (t : ℝ) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    ‖realCurveVelocity (fun c : ℝ => realExponentialMap g x (c • v)) t‖ = ‖v‖ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  have heq : (fun c : ℝ => realExponentialMap g x (c • v)) =
      (fun c => (realGeodesicFlow g p c).proj) :=
    funext (fun c => realExponentialMap_smul g x v c)
  rw [heq, realCurveVelocity_realGeodesic g (realGeodesicFlow g p)
    ((realGeodesicFlow_integral g p).isMIntegralCurveAt t)]
  rw [realExponentialMap_smul g x v t]
  have hE := realGeodesicFlow_energy g p t
  rw [realTangentEnergy_eq_norm_sq, realTangentEnergy_eq_norm_sq] at hE
  change ‖(realGeodesicFlow g p t).2‖ = ‖p.2‖
  nlinarith [norm_nonneg (realGeodesicFlow g p t).2, norm_nonneg p.2]

end Yau.LeafProofs.L12Aux
