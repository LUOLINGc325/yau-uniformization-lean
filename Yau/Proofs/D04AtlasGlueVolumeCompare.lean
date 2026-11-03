import Yau.Proofs.D04AtlasGlueVolume

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal Matrix

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_image_inverse_image (a : M.Carrier) {K : Set (ComplexVector n)}
    (hKt : K ⊆ chartTarget a) : chartPt a '' (chartInv a '' K) = K := by
  apply Subset.antisymm
  · rintro z ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    simpa only [chartPt, chartInv, (extChartAt (ComplexModel n) a).right_inv (hKt hw)] using hw
  · intro z hz
    exact ⟨chartInv a z, mem_image_of_mem _ hz,
      (extChartAt (ComplexModel n) a).right_inv (hKt hz)⟩

theorem inverse_image_subset_source (a : M.Carrier) {K : Set (ComplexVector n)}
    (hKt : K ⊆ chartTarget a) :
    chartInv a '' K ⊆ (extChartAt (ComplexModel n) a).source := by
  rintro x ⟨z, hz, rfl⟩
  exact (extChartAt (ComplexModel n) a).map_target (hKt hz)

theorem riemannianVolume_restrict_chart_compact
    (g : HermitianField M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    (a : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    μ.restrict (chartInv a '' K) =
      Measure.map (L18Aux.chartInvExtension a)
        (((lebesgueC n).restrict K).withDensity
          (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))) := by
  have hiK : IsCompact (chartInv a '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hKt)
  have hset : L18Aux.chartInvExtension a ⁻¹' (chartInv a '' K) ∩ chartTarget a = K := by
    rw [← L18Aux.chart_image_eq_extension_preimage,
      inter_eq_left.mpr (inverse_image_subset_source a hKt), chart_image_inverse_image a hKt]
  calc
    μ.restrict (chartInv a '' K) =
        (μ.restrict (extChartAt (ComplexModel n) a).source).restrict (chartInv a '' K) := by
      rw [Measure.restrict_restrict hiK.measurableSet,
        inter_eq_left.mpr (inverse_image_subset_source a hKt)]
    _ = _ := by
      rw [L18Aux.riemannianVolume_restrict_eq_map g μ hμ a,
        Measure.restrict_map (L18Aux.chartInvExtension_measurable a) hiK.measurableSet,
        restrict_withDensity ((L18Aux.chartInvExtension_measurable a) hiK.measurableSet),
        Measure.restrict_restrict ((L18Aux.chartInvExtension_measurable a) hiK.measurableSet), hset]

/-- Null assertions pull back on any coordinate compact with its actual
restriction of the original manifold volume. -/
theorem ae_chart_compact_pullback
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    {P : M.Carrier → Prop} (hP : ∀ᵐ x ∂μ.restrict (chartInv a '' K), P x) :
    ∀ᵐ z ∂(lebesgueC n).restrict K, P (chartInv a z) := by
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((volumeDensity_continuousOn g hg a).mono hKt).aemeasurable hK.measurableSet)
  rw [riemannianVolume_restrict_chart_compact g μ hμ a hK hKt] at hP
  have hpull := ae_of_ae_map (L18Aux.chartInvExtension_measurable a).aemeasurable hP
  rw [ae_withDensity_iff' hd] at hpull
  filter_upwards [hpull, ae_restrict_mem hK.measurableSet] with z hz hzK
  have hpos : ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (L12Aux.volumeDensity_pos g a z (hKt hzK))).ne'
  simpa only [L18Aux.chartInvExtension, ite_eq_left (hKt hzK)] using hz hpos

/-- The exact transport formula on a compact coordinate set. -/
theorem lintegral_chart_compact
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (f : M.Carrier → ℝ≥0∞) (hf : AEMeasurable f (μ.restrict (chartInv a '' K))) :
    ∫⁻ x in chartInv a '' K, f x ∂μ =
      ∫⁻ z in K, ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det) *
        f (chartInv a z) ∂lebesgueC n := by
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((volumeDensity_continuousOn g hg a).mono hKt).aemeasurable hK.measurableSet)
  rw [riemannianVolume_restrict_chart_compact g μ hμ a hK hKt] at hf ⊢
  have hfg : AEMeasurable (fun z => f (L18Aux.chartInvExtension a z))
      (((lebesgueC n).restrict K).withDensity
        (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))) :=
    hf.comp_measurable (L18Aux.chartInvExtension_measurable a)
  rw [lintegral_map' hf (L18Aux.chartInvExtension_measurable a).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀' hd hfg]
  apply setLIntegral_congr_fun hK.measurableSet
  intro z hz
  simp only [Pi.mul_apply, L18Aux.chartInvExtension, ite_eq_left (hKt hz)]

/-- Both comparisons use the original density and original inverse chart.
The constants are finite and the lower one is strictly positive. -/
theorem lintegral_chart_compact_bounds
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (f : M.Carrier → ℝ≥0∞), AEMeasurable f (μ.restrict (chartInv a '' K)) →
        ENNReal.ofReal c * (∫⁻ z in K, f (chartInv a z) ∂lebesgueC n) ≤
          ∫⁻ x in chartInv a '' K, f x ∂μ ∧
        (∫⁻ x in chartInv a '' K, f x ∂μ) ≤
          ENNReal.ofReal C * (∫⁻ z in K, f (chartInv a z) ∂lebesgueC n) := by
  obtain ⟨c, C, hc, hC, hb⟩ := volumeDensity_bounds g hg a hK hKt
  refine ⟨c, C, hc, hC, ?_⟩
  intro f hf
  rw [lintegral_chart_compact g hg μ hμ a hK hKt f hf]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hb z hz).1) le_rfl
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hb z hz).2) le_rfl

/-- Compact chart images of positive Lebesgue measure have positive volume. -/
theorem measure_chart_compact_pos
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (hpos : 0 < lebesgueC n K) : 0 < μ (chartInv a '' K) := by
  obtain ⟨c, C, hc, _, hb⟩ := lintegral_chart_compact_bounds g hg μ hμ a hK hKt
  have h := (hb (fun _ => 1) aemeasurable_const).1
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at h
  exact lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr hc, hpos⟩) h

/-- Compact-local error convergence transports from the coordinate measure
to the original manifold volume. Measurability is required only eventually
on the compact image, so early values outside the original domains are free. -/
theorem tendsto_lintegral_chart_compact_of_coordinate
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (f : ℕ → M.Carrier → ℝ≥0∞)
    (hf : ∀ᶠ j in atTop, AEMeasurable (f j) (μ.restrict (chartInv a '' K)))
    (ht : Tendsto (fun j => ∫⁻ z in K, f j (chartInv a z) ∂lebesgueC n) atTop (𝓝 0)) :
    Tendsto (fun j => ∫⁻ x in chartInv a '' K, f j x ∂μ) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hb⟩ := lintegral_chart_compact_bounds g hg μ hμ a hK hKt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun j => ENNReal.ofReal C *
      (∫⁻ z in K, f j (chartInv a z) ∂lebesgueC n)) atTop (𝓝 0) from by
        simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top))
    (Eventually.of_forall (fun _ => bot_le))
  exact hf.mono (fun j hj => (hb (f j) hj).2)

/-- The positive lower density also transports error convergence back to
Lebesgue measure in any original chart. -/
theorem tendsto_lintegral_coordinate_of_chart_compact
    (g : HermitianField M) (hg : MetricSmooth g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKt : K ⊆ chartTarget a)
    (f : ℕ → M.Carrier → ℝ≥0∞)
    (hf : ∀ᶠ j in atTop, AEMeasurable (f j) (μ.restrict (chartInv a '' K)))
    (ht : Tendsto (fun j => ∫⁻ x in chartInv a '' K, f j x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫⁻ z in K, f j (chartInv a z) ∂lebesgueC n) atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hb⟩ := lintegral_chart_compact_bounds g hg μ hμ a hK hKt
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hcinv : (ENNReal.ofReal c)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun j => (ENNReal.ofReal c)⁻¹ *
      (∫⁻ x in chartInv a '' K, f j x ∂μ)) atTop (𝓝 0) from by
        simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr hcinv))
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hf] with j hj
  have h := mul_le_mul' (le_refl ((ENNReal.ofReal c)⁻¹)) (hb (f j) hj).1
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_mul] using h

end Yau.Proofs.D04AtlasGlueAux
