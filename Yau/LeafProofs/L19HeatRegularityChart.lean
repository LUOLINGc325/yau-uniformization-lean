import Yau.LeafProofs.L19ScalarEnergyCompletion

/-! Actual local chart restrictions of scalar L² equivalence classes. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Compact chart regions have an internally obtained reciprocal density bound. -/
theorem scalarChart_density_bound (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget x) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      1 ≤ C * Real.sqrt (realMetricFn g.form x z).det := by
  let ρ := fun z => Real.sqrt (realMetricFn g.form x z).det
  have hρpos (z) (hz : z ∈ K) : 0 < ρ z := L12Aux.volumeDensity_pos g.form x z (hKt hz)
  have hc : ContinuousOn (fun z => (ρ z)⁻¹) K :=
    ((volumeDensity_contDiffOn g x).continuousOn.mono hKt).inv₀
      (fun z hz => ne_of_gt (hρpos z hz))
  obtain ⟨c, hc⟩ := hK.bddAbove_image hc
  refine ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have hh : (ρ z)⁻¹ ≤ max c 1 := (hc ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_right hh (hρpos z hz).le
  rw [inv_mul_cancel₀ (ne_of_gt (hρpos z hz))] at hm
  exact hm

/-- The inverse chart sends unweighted local volume to a bounded multiple
of the actual manifold volume. The constant is a bound for the reciprocal
of the computed metric density. -/
theorem scalarChart_map_volume_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, 1 ≤ C * Real.sqrt (realMetricFn g.form x z).det) :
    Measure.map (chartInvExtension x) (volume.restrict O) ≤ ENNReal.ofReal C • μ := by
  let ρ := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form x z).det)
  let ν : Measure (ComplexVector n) := volume.restrict O
  let νt : Measure (ComplexVector n) := volume.restrict (chartTarget x)
  have hν : ν ≤ ENNReal.ofReal C • ν.withDensity ρ := by
    calc
      ν = ν.withDensity (fun _ => 1) := withDensity_one.symm
      _ ≤ ν.withDensity (ENNReal.ofReal C • ρ) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem hO] with z hz
        change 1 ≤ ENNReal.ofReal C * ENNReal.ofReal _
        rw [← ENNReal.ofReal_mul hC]
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hbound z hz)
      _ = _ := withDensity_smul' _ _ ENNReal.ofReal_ne_top
  have hνt : ν.withDensity ρ ≤ νt.withDensity ρ := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [withDensity_apply _ hs, withDensity_apply _ hs]
    exact lintegral_mono' (Measure.restrict_mono le_rfl (Measure.restrict_mono hOt le_rfl)) le_rfl
  have hm := Measure.map_mono
    (hν.trans (_root_.smul_le_smul_left (ENNReal.ofReal C) hνt)) (chartInvExtension_measurable x)
  rw [Measure.map_smul _ (chartInvExtension_measurable x).aemeasurable] at hm
  have heq : Measure.map (chartInvExtension x) (νt.withDensity ρ) =
      μ.restrict (extChartAt (ComplexModel n) x).source := by
    rw [riemannianVolume_restrict_eq_map g.form μ hμ x, lebesgueC_eq_volume]
  rw [heq] at hm
  exact hm.trans (_root_.smul_le_smul_left (ENNReal.ofReal C) Measure.restrict_le_self)

/-- Bounded restriction to a chart, constructed on the actual scalar L²
quotient. No choice of pointwise representative is part of its input. -/
def scalarChartRestrictionCLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, 1 ≤ C * Real.sqrt (realMetricFn g.form x z).det) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  let ν := volume.restrict O
  let F := chartInvExtension x
  let hF : MeasurePreserving F ν (Measure.map F ν) :=
    ⟨chartInvExtension_measurable x, rfl⟩
  (Lp.compMeasurePreservingₗᵢ ℝ F hF).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (scalarChart_map_volume_le g μ hμ x hO hOt hC hbound))

/-- The bounded restriction agrees with the actual inverse-chart function
almost everywhere in unweighted local Euclidean volume. -/
theorem scalarChartRestrictionCLM_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, 1 ≤ C * Real.sqrt (realMetricFn g.form x z).det)
    (f : Lp ℝ 2 μ) :
    scalarChartRestrictionCLM g μ hμ x hO hOt hC hbound f =ᵐ[volume.restrict O]
      (fun z => f (chartInv x z)) := by
  let ν := volume.restrict O
  let F := chartInvExtension x
  let hF : MeasurePreserving F ν (Measure.map F ν) :=
    ⟨chartInvExtension_measurable x, rfl⟩
  have hcoe := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (scalarChart_map_volume_le g μ hμ x hO hOt hC hbound) f
  have hcomp := hF.quasiMeasurePreserving.ae_eq_comp hcoe
  have hrestrict := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (scalarChart_map_volume_le g μ hμ x hO hOt hC hbound) f) hF
  filter_upwards [hrestrict, hcomp, ae_restrict_mem hO] with z hz hzc hzO
  exact hz.trans (hzc.trans (by simp only [Function.comp_apply, F, chartInvExtension, ite_eq_left (hOt hzO)]))

/-- The operator bound is the square root of the genuine chart measure
comparison constant. -/
theorem scalarChartRestrictionCLM_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : MeasurableSet O) (hOt : O ⊆ chartTarget x)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ O, 1 ≤ C * Real.sqrt (realMetricFn g.form x z).det) :
    ‖scalarChartRestrictionCLM g μ hμ x hO hOt hC hbound‖ ≤ C ^ (1 / 2 : ℝ) := by
  unfold scalarChartRestrictionCLM
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h₁ := (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ (chartInvExtension x)
    (show MeasurePreserving (chartInvExtension x) (volume.restrict O)
      (Measure.map (chartInvExtension x) (volume.restrict O)) from
        ⟨chartInvExtension_measurable x, rfl⟩)).norm_toContinuousLinearMap_le
  have h₂ := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2)
    ENNReal.ofReal_ne_top (scalarChart_map_volume_le g μ hμ x hO hOt hC hbound)
  calc
    _ ≤ 1 * (ENNReal.ofReal C).toReal ^ (1 / (2 : ENNReal)).toReal :=
      mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one
    _ = _ := by simp only [one_mul, ENNReal.toReal_ofReal hC]; norm_num

/-- Chart restriction on any relatively compact actual chart region,
with every norm comparison constructed internally. -/
def scalarEnergy_chartRestrictionCLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
  let hC := (scalarChart_density_bound g x hOc hOt).choose_spec
  scalarChartRestrictionCLM g μ hμ x hO.measurableSet (subset_closure.trans hOt)
    hC.1.le (fun z hz => hC.2 z (subset_closure hz))

theorem scalarEnergy_chartRestrictionCLM_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (f : Lp ℝ 2 μ) :
    scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt f =ᵐ[volume.restrict O]
      (fun z => f (chartInv x z)) :=
  scalarChartRestrictionCLM_coe g μ hμ x hO.measurableSet (subset_closure.trans hOt)
    (scalarChart_density_bound g x hOc hOt).choose_spec.1.le
    (fun z hz => (scalarChart_density_bound g x hOc hOt).choose_spec.2 z (subset_closure hz)) f

/-- Genuine inverse-chart restriction respects arbitrary actual-volume
AE equalities. -/
theorem scalarEnergy_chart_ae_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {F : Type*} {f k : M.Carrier → F}
    (hfk : f =ᵐ[μ] k) : (fun z => f (chartInv x z)) =ᵐ[volume.restrict O]
      (fun z => k (chartInv x z)) := by
  let hC := (scalarChart_density_bound g x hOc hOt).choose_spec
  have hm := scalarChart_map_volume_le g μ hμ x hO.measurableSet (subset_closure.trans hOt)
    hC.1.le (fun z hz => hC.2 z (subset_closure hz))
  have hq : QuasiMeasurePreserving (chartInvExtension x) (volume.restrict O) μ :=
    ⟨chartInvExtension_measurable x, Measure.absolutelyContinuous_of_le_smul hm⟩
  filter_upwards [hq.ae_eq_comp hfk, ae_restrict_mem hO.measurableSet] with z hz hzO
  simpa only [Function.comp_apply, chartInvExtension,
    ite_eq_left ((subset_closure.trans hOt) hzO)] using hz

/-- On the true energy core, chart restriction of J is the original smooth
scalar in the original chart. -/
theorem scalarEnergy_chartRestrictionCLM_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
      (scalarEnergyL2 g μ hμ (f : ScalarEnergySpace g μ hμ)) =ᵐ[volume.restrict O]
        inChart x f := by
  rw [scalarEnergyL2_coe]
  exact (scalarEnergy_chartRestrictionCLM_coe g μ hμ x hO hOc hOt _).trans
    (scalarEnergy_chart_ae_eq g μ hμ x hO hOc hOt (scalarEnergyDomainL2_coe g μ hμ f))

end Yau.LeafProofs.L19Aux
