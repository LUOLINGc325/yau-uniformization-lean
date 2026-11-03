import Yau.LeafProofs.L03DiracCompact

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The real chart map with a measurable zero extension off its source. -/
def realChartPtExtension (x y : M.Carrier) : ComplexVector n :=
  @ite _ (y ∈ (extChartAt (ComplexModel n) x).source) (Classical.propDecidable _) (chartPt x y) 0

theorem realChartPtExtension_measurable (x : M.Carrier) : Measurable (realChartPtExtension x) := by
  classical
  change Measurable (((extChartAt (ComplexModel n) x).source).piecewise (chartPt x) (fun _ => 0))
  exact (continuousOn_extChartAt (I := ComplexModel n) x).measurable_piecewise
    (continuousOn_const (c := (0 : ComplexVector n))) (isOpen_extChartAt_source x).measurableSet

theorem chartPt_image_extension_preimage (x : M.Carrier) (s : Set (ComplexVector n)) :
    chartPt x '' (realChartPtExtension x ⁻¹' s ∩ (extChartAt (ComplexModel n) x).source) =
      s ∩ chartTarget x := by
  ext z
  constructor
  · rintro ⟨y, ⟨hys, hy⟩, rfl⟩
    refine ⟨?_, (extChartAt (ComplexModel n) x).map_source hy⟩
    simpa only [Set.mem_preimage, realChartPtExtension, if_pos hy] using hys
  · rintro ⟨hzs, hz⟩
    have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
      (extChartAt (ComplexModel n) x).map_target hz
    refine ⟨chartInv x z, ⟨?_, hy⟩, (extChartAt (ComplexModel n) x).right_inv hz⟩
    change realChartPtExtension x (chartInv x z) ∈ s
    have hzid : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
    rw [realChartPtExtension, if_pos hy, hzid]
    exact hzs

/-- The original volume pushed through the real chart is exactly the
existing positive metric density times restricted Euclidean volume. -/
theorem map_realChartPtExtension_volume (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (x : M.Carrier) :
    (μ.restrict (extChartAt (ComplexModel n) x).source).map (realChartPtExtension x) =
      ((lebesgueC n).restrict (chartTarget x)).withDensity
        (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g x z).det)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (realChartPtExtension_measurable x) hs,
    Measure.restrict_apply ((realChartPtExtension_measurable x) hs), withDensity_apply _ hs,
    Measure.restrict_restrict hs]
  rw [hμ x _ (((realChartPtExtension_measurable x) hs).inter (isOpen_extChartAt_source x).measurableSet)
    (by intro y hy; simpa only [extChartAt_source] using hy.2), chartPt_image_extension_preimage]

theorem realChartPtExtension_quasiMeasurePreserving (g : HermitianField M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g μ) (x : M.Carrier) :
    QuasiMeasurePreserving (realChartPtExtension x) (μ.restrict (extChartAt (ComplexModel n) x).source)
      ((lebesgueC n).restrict (chartTarget x)) := by
  refine ⟨realChartPtExtension_measurable x, ?_⟩
  rw [map_realChartPtExtension_volume g μ hμ x]
  exact withDensity_absolutelyContinuous _ _

/-- Unweighted Euclidean chart AE strong measurability descends to the
actual Riemannian volume for a section vanishing off that source. -/
theorem aestronglyMeasurable_of_chartInv_zero_off (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {F : Type*} [NormedAddCommGroup F] {f : M.Carrier → F}
    (hzero : ∀ y, y ∉ (extChartAt (ComplexModel n) x).source → f y = 0)
    (hf : AEStronglyMeasurable (fun z => f (chartInv x z))
      ((lebesgueC n).restrict (chartTarget x))) : AEStronglyMeasurable f μ := by
  have hs : MeasurableSet (extChartAt (ComplexModel n) x).source :=
    (isOpen_extChartAt_source x).measurableSet
  have hm := hf.comp_quasiMeasurePreserving (realChartPtExtension_quasiMeasurePreserving g.form μ hμ x)
  have hms : AEStronglyMeasurable f (μ.restrict (extChartAt (ComplexModel n) x).source) := by
    apply hm.congr
    filter_upwards [ae_restrict_mem hs] with y hy
    change f (chartInv x (realChartPtExtension x y)) = f y
    have hyid : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
    rw [realChartPtExtension, if_pos hy, hyid]
  have hi := (aestronglyMeasurable_indicator_iff hs).mpr hms
  apply hi.congr
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · exact Set.indicator_of_mem hy f
    · rw [Set.indicator_of_notMem hy, hzero y hy]

/-- The reverse actual-volume integrability transport, with only an AE
strongly measurable representative and exact zero extension off the chart. -/
theorem integrable_of_chart_volume_zero_off (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M.Carrier → F}
    (hzero : ∀ y, y ∉ (extChartAt (ComplexModel n) x).source → f y = 0)
    (hfm : AEStronglyMeasurable (fun z => f (chartInv x z))
      ((lebesgueC n).restrict (chartTarget x)))
    (hf : IntegrableOn (fun z => Real.sqrt (realMetricFn g.form x z).det • f (chartInv x z))
      (chartTarget x) (lebesgueC n)) : Integrable f μ := by
  let ν := (lebesgueC n).restrict (chartTarget x)
  let d := fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g.form x z).det)
  have ht : MeasurableSet (chartTarget x) := (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  have hs : MeasurableSet (extChartAt (ComplexModel n) x).source := (isOpen_extChartAt_source x).measurableSet
  have hd : AEMeasurable d ν := ENNReal.measurable_ofReal.comp_aemeasurable
    ((L18Aux.volumeDensity_continuousOn g x).aemeasurable ht)
  have hma := aestronglyMeasurable_of_chartInv_zero_off g μ hμ x hzero hfm
  have hmap : AEStronglyMeasurable f (Measure.map (L18Aux.chartInvExtension x) (ν.withDensity d)) := by
    rw [← L18Aux.riemannianVolume_restrict_eq_map g.form μ hμ x]
    exact hma.mono_measure Measure.restrict_le_self
  have hi : Integrable f (μ.restrict (extChartAt (ComplexModel n) x).source) := by
    rw [L18Aux.riemannianVolume_restrict_eq_map g.form μ hμ x]
    apply (integrable_map_measure hmap (L18Aux.chartInvExtension_measurable x).aemeasurable).mpr
    apply (integrable_withDensity_iff_integrable_smul₀' hd
      (ae_of_all ν fun _ => ENNReal.ofReal_lt_top)).mpr
    apply hf.congr
    filter_upwards [ae_restrict_mem ht] with z hz
    simp only [d, Function.comp_apply, L18Aux.chartInvExtension, if_pos hz,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hiI := (integrable_indicator_iff hs).mpr hi
  apply hiI.congr
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · exact Set.indicator_of_mem hy f
    · rw [Set.indicator_of_notMem hy, hzero y hy]

/-- Arbitrary AE strongly measurable model fields have AE strongly
measurable scalar chart pushforwards in the actual manifold volume. -/
theorem chartPushforwardZero_aestronglyMeasurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {F : Type*} [NormedAddCommGroup F] (P : ComplexVector n → F)
    (hP : AEStronglyMeasurable P (lebesgueC n)) :
    AEStronglyMeasurable (L18Aux.chartPushforwardZero x P) μ := by
  apply aestronglyMeasurable_of_chartInv_zero_off g μ hμ x
  · intro y hy
    simp only [L18Aux.chartPushforwardZero, if_neg hy]
  · apply (hP.mono_measure Measure.restrict_le_self).congr
    filter_upwards [ae_restrict_mem (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet] with z hz
    exact (L18Aux.chartPushforwardZero_chartInv x P hz).symm

end Yau.LeafProofs.L03
