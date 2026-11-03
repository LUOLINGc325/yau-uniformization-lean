import Yau.Proofs.P06LocalCauchyLimitJetMaps

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.LocalCauchyLimit
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}
local instance : NormedAddCommGroup (HodgeJets.Fiber n k) := inferInstance
local instance : NormedSpace ℝ (HodgeJets.Fiber n k) := inferInstance
local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] HodgeJets.Fiber n k) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] HodgeJets.Fiber n k) := inferInstance
local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] HodgeJets.Fiber n k) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] HodgeJets.Fiber n k) := inferInstance

theorem smooth_slice (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Ioi 0))
    {t : ℝ} (ht : 0 < t) : SmoothRealForm (U t) := by
  intro x I
  exact (hU x I).comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz,ht⟩)

theorem spatialModelJet_tendsto (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hU : SmoothFormTime U (Ioi 0))
    (hl : JointJetLimit Us U) (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (m : ℕ) :
    Tendsto (fun j => iteratedFDeriv ℝ m (chartForm (Us j t) x) z) atTop
      (𝓝 (iteratedFDeriv ℝ m (chartForm (U t) x) z)) := by
  let L := ContinuousLinearMap.inl ℝ (ComplexVector n) ℝ
  let R : ((ComplexVector n × ℝ) [×m]→L[ℝ] HodgeJets.Fiber n k) →L[ℝ]
      (ComplexVector n) [×m]→L[ℝ] HodgeJets.Fiber n k :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => L)
  have h := (R.continuous.tendsto _).comp (jointModelJet_tendsto Us U hUs hU hl x z hz t ht m)
  have hs (V : ℝ → RealForm M k) (hV : SmoothFormTime V (Ioi 0)) :
      ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => chartForm (V p.2) x p.1)
        (chartTarget x ×ˢ Ioi 0) := (modelForm_contDiffOn_iff _ _).mpr (fun I => hV x I)
  have heq (V : ℝ → RealForm M k) (hV : SmoothFormTime V (Ioi 0)) :=
    slice_iteratedFDeriv ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi)
      (hs V hV) (show (z,t) ∈ chartTarget x ×ˢ Ioi 0 from ⟨hz,ht⟩) m
  convert h using 1
  · funext j
    exact heq (Us j) (hUs j)
  · exact congrArg nhds (heq U hU)

theorem hodgeComponents_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hU : SmoothFormTime U (Ioi 0))
    (hl : JointJetLimit Us U) (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (I : Fin k → RIdx n) :
    Tendsto (fun j => formComponents (hodgeRealForm g.form k (Us j t)) x z I) atTop
      (𝓝 (formComponents (hodgeRealForm g.form k (U t)) x z I)) := by
  have h0 : Tendsto (fun j => chartForm (Us j t) x z) atTop (𝓝 (chartForm (U t) x z)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (ComplexVector n) (HodgeJets.Fiber n k)).continuous.tendsto _).comp
      (spatialModelJet_tendsto Us U hUs hU hl x z hz t ht 0)
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h
  have h1 : Tendsto (fun j => fderiv ℝ (chartForm (Us j t) x) z) atTop
      (𝓝 (fderiv ℝ (chartForm (U t) x) z)) := by
    have h := ((continuousMultilinearCurryFin1 ℝ (ComplexVector n) (HodgeJets.Fiber n k)).continuous.tendsto _).comp
      (spatialModelJet_tendsto Us U hUs hU hl x z hz t ht 1)
    simpa only [Function.comp_def,firstCurry_actual] using h
  have h2 : Tendsto (fun j => fderiv ℝ (fderiv ℝ (chartForm (Us j t) x)) z) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ (chartForm (U t) x)) z)) := by
    have h := ((secondCurry (E := ComplexVector n) (F := HodgeJets.Fiber n k)).continuous.tendsto _).comp
      (spatialModelJet_tendsto Us U hUs hU hl x z hz t ht 2)
    simpa only [Function.comp_def,secondCurry_actual] using h
  have h := ((HodgeJets.hodgeSecondJetCLM g.form x z k).continuous.tendsto _).comp
    (h0.prodMk_nhds (h1.prodMk_nhds h2))
  have hmodel : Tendsto (fun j => chartForm (hodgeRealForm g.form k (Us j t)) x z) atTop
      (𝓝 (chartForm (hodgeRealForm g.form k (U t)) x z)) := by
    convert h using 1
    · funext j
      exact HodgeJets.hodgeSecondJetCLM_chart g μ hμ (Us j t) (smooth_slice _ (hUs j) ht) x hz
    · exact congrArg nhds (HodgeJets.hodgeSecondJetCLM_chart g μ hμ (U t) (smooth_slice U hU ht) x hz)
  have he := ((ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
    (fun r => realVec (I r))).continuous.tendsto _).comp hmodel
  exact he

theorem generator_eq_hodge (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x) (I : Fin k → RIdx n) :
    hodgeGeneratorComponents g.form x (formComponents A x) z I =
      -formComponents (hodgeRealForm g.form k A) x z I / 2 := by
  unfold hodgeGeneratorComponents
  rw [hodgeRealForm_represents g μ hμ A hA x z hz I]

theorem time_hasDerivAt (U : ℝ → RealForm M k) (hU : SmoothFormTime U (Ioi 0))
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (I : Fin k → RIdx n) :
    HasDerivAt (fun s => formComponents (U s) x z I)
      (fderiv ℝ (fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I) (z,t) (0,1)) t := by
  have hp : (z,t) ∈ chartTarget x ×ˢ Ioi 0 := ⟨hz,ht⟩
  have h := ((hU x I).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi).mem_nhds hp)).differentiableAt (by simp)
  exact h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))

/-- The original calculated heat equation passes through the actual smooth
local limit by continuity of the true second-jet Hodge calculator. -/
theorem formHeatEquation_limit (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hU : SmoothFormTime U (Ioi 0))
    (hl : JointJetLimit Us U) (hPDE : ∀ j, Blueprint.FormHeatEquation g.form (Us j)) :
    Blueprint.FormHeatEquation g.form U := by
  intro x z hz t ht I
  have hgen : Tendsto (fun j => hodgeGeneratorComponents g.form x (formComponents (Us j t) x) z I)
      atTop (𝓝 (hodgeGeneratorComponents g.form x (formComponents (U t) x) z I)) := by
    simp_rw [generator_eq_hodge g μ hμ (Us _ t) (smooth_slice _ (hUs _) ht) x z hz I,
      generator_eq_hodge g μ hμ (U t) (smooth_slice U hU ht) x z hz I]
    exact (hodgeComponents_tendsto g μ hμ Us U hUs hU hl x z hz t ht I).neg.div_const 2
  have htime := ((continuousMultilinearCurryFin1 ℝ (ComplexVector n × ℝ) ℝ).continuous.tendsto _).comp
    (jointJet_tendsto Us U hUs hU hl x z hz t ht I 1)
  simp only [Function.comp_def,firstCurry_actual] at htime
  have hval := ((ContinuousLinearMap.apply ℝ ℝ ((0,1) : ComplexVector n × ℝ)).continuous.tendsto _).comp htime
  have heq (j : ℕ) := (time_hasDerivAt (Us j) (hUs j) x z hz t ht I).unique (hPDE j x z hz t ht I)
  have hlim := hval.congr' (Eventually.of_forall heq)
  have hderiv := time_hasDerivAt U hU x z hz t ht I
  have hEq := tendsto_nhds_unique hlim hgen
  change (fderiv ℝ (fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I) (z,t) (0,1)) =
    hodgeGeneratorComponents g.form x (formComponents (U t) x) z I at hEq
  rw [hEq] at hderiv
  exact hderiv

theorem exists_formHeat_limit (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Us : ℕ → ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hc : JointJetCauchy Us)
    (hPDE : ∀ j, Blueprint.FormHeatEquation g.form (Us j)) (A : RealForm M k) :
    ∃ U : ℝ → RealForm M k, U 0 = A ∧ SmoothFormTime U (Ioi 0) ∧
      JointJetLimit Us U ∧ Blueprint.FormHeatEquation g.form U := by
  obtain ⟨U,hU0,hU,hl⟩ := exists_smooth_limit Us hUs hc A
  exact ⟨U,hU0,hU,hl,formHeatEquation_limit g μ hμ Us U hUs hU hl hPDE⟩

end Yau.NodeProofs.P06Aux.LocalCauchyLimit
