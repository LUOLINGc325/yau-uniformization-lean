import Yau.LeafProofs.L12Continuation

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option backward.isDefEq.respectTransparency false in
theorem realTangentCoords_self (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) : realTangentCoords x x v = v := by
  letI := manifold_realSmooth M
  unfold realTangentCoords
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source _ _)]
  exact tangentCoordChange_self (I := 𝓘(ℝ, ComplexVector n)) (mem_extChartAt_source x)

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_realPhase_proj
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    mfderiv (realPhaseModel n) 𝓘(ℝ, ComplexVector n)
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj) p =
      ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  have hf : MDifferentiableAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n)
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj) p :=
    (Bundle.contMDiffAt_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n)) (p := p)).mdifferentiableAt (by simp)
  have heq : writtenInExtChartAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n) p
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj)
      =ᶠ[𝓝 (extChartAt (realPhaseModel n) p p)] Prod.fst := by
    filter_upwards [(isOpen_extChartAt_target (I := realPhaseModel n) p).mem_nhds
      (mem_extChartAt_target p)] with q hq
    have hz := (realPhaseChart_target p q).mp hq
    change chartPt p.proj (((extChartAt (realPhaseModel n) p).symm q).proj) = q.1
    rw [realPhasePoint_eq_extChartAt_symm p q hz]
    exact (extChartAt (ComplexModel n) p.proj).right_inv hz
  rw [hf.mfderiv_abuse, ModelWithCorners.range_eq_univ, fderivWithin_univ,
    heq.fderiv_eq, (hasFDerivAt_fst (p := extChartAt (realPhaseModel n) p p)).fderiv]

set_option backward.isDefEq.respectTransparency false in
theorem realCurveVelocity_realGeodesic (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveAt γ (realGeodesicSpray g) t₀ →
      realCurveVelocity (fun t => (γ t).proj) t₀ = (γ t₀).2 := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ
  have hf : MDifferentiableAt (realPhaseModel n) 𝓘(ℝ, ComplexVector n)
      (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj) (γ t₀) :=
    (Bundle.contMDiffAt_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n)) (p := γ t₀)).mdifferentiableAt (by simp)
  have hc := hf.hasMFDerivAt.comp t₀ hγ.hasMFDerivAt
  unfold realCurveVelocity
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
    ((fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj) ∘ γ) t₀
    ((tangentSpaceCastModel 𝓘(ℝ, ℝ) t₀).symm 1) = _
  rw [hc.mfderiv]
  change mfderiv (realPhaseModel n) 𝓘(ℝ, ComplexVector n)
    (fun q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier => q.proj) (γ t₀)
    (((1 : ℝ →L[ℝ] ℝ).smulRight (realGeodesicSpray g (γ t₀))) 1) = _
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
    mfderiv_realPhase_proj]

  exact realTangentCoords_self (γ t₀).proj (γ t₀).2


theorem realGeodesic_chart_eventually (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveAt γ (realGeodesicSpray g) t₀ →
      ∀ᶠ t in 𝓝 t₀,
        (extChartAt (realPhaseModel n) (γ t₀) (γ t)).1 ∈ chartTarget (γ t₀).proj ∧
        HasDerivAt (extChartAt (realPhaseModel n) (γ t₀) ∘ γ)
          (chartGeodesicSpray g.form (γ t₀).proj
            (extChartAt (realPhaseModel n) (γ t₀) (γ t))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ
  filter_upwards [hγ.eventually_hasDerivAt,
    hγ.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := realPhaseModel n) (γ t₀))] with t ht hsource
  refine ⟨(realPhaseChart_target (γ t₀) _).mp
    ((extChartAt (realPhaseModel n) (γ t₀)).map_source hsource), ?_⟩
  rwa [tangentCoordChange_realGeodesicSpray g (γ t₀) (γ t) hsource] at ht

theorem realGeodesic_contMDiffAt (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {t₀ : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveAt γ (realGeodesicSpray g) t₀ →
      ContMDiffAt 𝓘(ℝ, ℝ) (realPhaseModel n) ∞ γ t₀ := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  intro hγ
  let p := γ t₀
  let η := extChartAt (realPhaseModel n) p ∘ γ
  obtain ⟨δ, hδ, hδsol⟩ := Metric.mem_nhds_iff.mp (realGeodesic_chart_eventually g γ hγ)
  have hcc : Set.Icc (t₀ - δ / 2) (t₀ + δ / 2) ⊆ Metric.ball t₀ δ := by
    intro t ht
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hηsmooth : ContDiffOn ℝ ∞ η (Set.Icc (t₀ - δ / 2) (t₀ + δ / 2)) :=
    chartGeodesic_contDiffOn_Icc g p.proj η (fun t ht => hδsol (hcc ht))
  have hηat : ContDiffAt ℝ ∞ η t₀ :=
    hηsmooth.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  have hi := contMDiffWithinAt_extChartAt_symm_range
    (I := realPhaseModel n) (n := ∞) p (mem_extChartAt_target p)
  rw [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] at hi
  have hcom := hi.comp t₀ hηat.contMDiffAt
  apply hcom.congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds (I := realPhaseModel n) p)] with t ht
  exact ((extChartAt (realPhaseModel n) p).left_inv ht).symm


theorem realGeodesic_inducedDistance_le (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {a b s t : ℝ} :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    IsMIntegralCurveOn γ (realGeodesicSpray g) (Set.Ioo a b) →
      s ∈ Set.Ioo a b → t ∈ Set.Ioo a b → s ≤ t →
        inducedDistance g.form (γ s).proj (γ t).proj ≤
          Real.sqrt (realTangentEnergy g.form (γ s)) * (t - s) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hγ hs ht hst
  let β := fun r => (γ r).proj
  have hsub : Set.Icc s t ⊆ Set.Ioo a b :=
    fun r hr => ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hBetaSmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) ∞ β (Set.Icc s t) := by
    intro r hr
    have hr' := hsub hr
    have hphase := realGeodesic_contMDiffAt g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr'.1 hr'.2))
    exact ((Bundle.contMDiffAt_proj (IB := 𝓘(ℝ, ComplexVector n)) (n := ∞)
      (TangentSpace 𝓘(ℝ, ComplexVector n)) (p := γ r)).comp r hphase).contMDiffWithinAt
  have hβ := hBetaSmooth.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hspeed : ∀ r ∈ Set.Icc s t, ‖realCurveVelocity β r‖ =
      Real.sqrt (realTangentEnergy g.form (γ s)) := by
    intro r hr
    have hr' := hsub hr
    change ‖realCurveVelocity (fun r => (γ r).proj) r‖ = _
    rw [realCurveVelocity_realGeodesic g γ
      (hγ.isMIntegralCurveAt (Ioo_mem_nhds hr'.1 hr'.2))]
    calc
      ‖(γ r).2‖ = Real.sqrt (‖(γ r).2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by
        rw [← realTangentEnergy_eq_norm_sq g.form (γ r)]
        exact congrArg Real.sqrt (realGeodesicEnergy_constant g γ hγ hr' hs)
  have hd : ENNReal.ofReal (inducedDistance g.form (β s) (β t)) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) β s t := by
    rw [inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength hβ rfl rfl hst
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) β s t =
      ENNReal.ofReal (Real.sqrt (realTangentEnergy g.form (γ s)) * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hconst : (fun r => ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) β r 1‖ₑ)
        =ᵐ[volume.restrict (Set.Icc s t)]
        (fun _ => ENNReal.ofReal (Real.sqrt (realTangentEnergy g.form (γ s)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      change ‖realCurveVelocity β r‖ₑ = _
      rw [← ofReal_norm, hspeed r hr]
    rw [lintegral_congr_ae hconst, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Icc, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [hlen] at hd
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hst))).mp hd

theorem realGeodesic_distFrom_le (g : SmoothMetric M)
    (γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) {a t : ℝ} (ha : 0 < a) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    γ 0 = p → IsMIntegralCurveOn γ (realGeodesicSpray g) (Set.Ioo (-a) a) →
      t ∈ Set.Ioo (-a) a → inducedDistance g.form p.proj (γ t).proj ≤
        Real.sqrt (realTangentEnergy g.form p) * |t| := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  intro hγ0 hγ ht
  have h0 : (0 : ℝ) ∈ Set.Ioo (-a) a := ⟨by linarith, ha⟩
  by_cases ht0 : 0 ≤ t
  · have hd := realGeodesic_inducedDistance_le g γ hγ h0 ht ht0
    simpa only [hγ0, sub_zero, abs_of_nonneg ht0] using hd
  · have htneg := lt_of_not_ge ht0
    have hd := realGeodesic_inducedDistance_le g γ hγ ht h0 htneg.le
    have hE := realGeodesicEnergy_constant g γ hγ ht h0
    rw [hγ0] at hE
    calc
      inducedDistance g.form p.proj (γ t).proj =
          inducedDistance g.form (γ t).proj (γ 0).proj := by
        rw [hγ0]
        exact g.induced_distance_symm _ _
      _ ≤ Real.sqrt (realTangentEnergy g.form (γ t)) * (0 - t) := hd
      _ = _ := by rw [hE, zero_sub, abs_of_neg htneg]

/-- The actual tangent-bundle topology is Hausdorff: distinct base points
are separated on the base, and points in one fiber are separated in a common
bundle trivialization. -/
theorem realPhase_t2Space (M : ComplexManifold n) :
    letI := manifold_realSmooth M
    T2Space (TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) := by
  letI := manifold_realSmooth M
  apply t2Space_iff_disjoint_nhds.mpr
  intro p q hpq
  by_cases hbase : p.proj = q.proj
  · let e := trivializationAt (ComplexVector n) (TangentSpace 𝓘(ℝ, ComplexVector n)) p.proj
    have hpbase : p.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hqbase : q.proj ∈ e.baseSet := by rwa [← hbase]
    have hp : p ∈ e.source := e.mem_source.mpr hpbase
    have hq : q ∈ e.source := e.mem_source.mpr hqbase
    have he : e p ≠ e q := fun h => hpq (e.toOpenPartialHomeomorph.injOn hp hq h)
    exact (e.toOpenPartialHomeomorph.continuousAt hp).disjoint
      (disjoint_nhds_nhds.mpr he) (e.toOpenPartialHomeomorph.continuousAt hq)
  · exact (FiberBundle.continuous_proj (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (FiberBundle.continuous_proj (ComplexVector n)
        (TangentSpace 𝓘(ℝ, ComplexVector n))).continuousAt

/-- Completeness of the original length distance gives genuine global
Levi--Civita geodesics, represented as integral curves of the actual spray. -/
theorem exists_global_realGeodesic (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) :
    letI := manifold_realSmooth M
    letI := manifold_realPhase M
    ∃ γ : ℝ → TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier,
      γ 0 = p ∧ IsMIntegralCurve γ (realGeodesicSpray g) := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI := realPhaseModel_boundaryless n
  letI := realPhase_t2Space M
  have hv := (realGeodesicSpray_contMDiff g).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  apply exists_global_integral_curve_of_compact_trapping hv p
  intro T hT
  let E₀ := realTangentEnergy g.form p
  let c := Real.sqrt E₀
  let Kbase : Set M.Carrier := {x | inducedDistance g.form p.proj x ≤ c * T}
  have hKbase : IsCompact Kbase := isCompact_inducedDistance_sublevel g p.proj (c * T)
  refine ⟨{q | q.proj ∈ Kbase ∧ realTangentEnergy g.form q ≤ E₀},
    isCompact_realTangentEnergy_sublevel g hKbase E₀, ?_⟩
  intro a ha haT γ hγ0 hγ t ht
  have h0 : (0 : ℝ) ∈ Set.Ioo (-a) a := ⟨by linarith, ha⟩
  have hE := realGeodesicEnergy_constant g γ hγ ht h0
  rw [hγ0] at hE
  refine ⟨?_, hE.le⟩
  have hd := realGeodesic_distFrom_le g γ p ha hγ0 hγ ht
  exact hd.trans (mul_le_mul_of_nonneg_left
    ((abs_lt.mpr ht).le.trans haT) (Real.sqrt_nonneg E₀))

end Yau.LeafProofs.L12Aux
