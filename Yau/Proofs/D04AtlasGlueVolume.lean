import Yau.Proofs.G02GluedVolume
import Yau.LeafProofs.L12
import Yau.Proofs.D04Anchors

open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal Matrix

noncomputable section

namespace Yau.Proofs.D04AtlasGlueAux

open Yau Yau.Blueprint Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

/-- The density in the original volume law is continuous under precisely
`MetricSmooth`; no completeness or Kähler data is used. -/
theorem volumeDensity_continuousOn (g : HermitianField M) (hg : MetricSmooth g)
    (a : M.Carrier) :
    ContinuousOn (fun z => Real.sqrt (realMetricFn g a z).det) (chartTarget a) :=
  (L18Aux.contDiffOn_matrix_det (hg a)).continuousOn.sqrt

/-- On a coordinate compact the actual density has positive finite bounds. -/
theorem volumeDensity_bounds (g : HermitianField M) (hg : MetricSmooth g)
    (a : M.Carrier) {K : Set (ComplexVector n)}
    (hK : IsCompact K) (hKt : K ⊆ chartTarget a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z ∈ K, c ≤ Real.sqrt (realMetricFn g a z).det ∧
        Real.sqrt (realMetricFn g a z).det ≤ C := by
  have hd := (volumeDensity_continuousOn g hg a).mono hKt
  obtain ⟨c, hc, hlower⟩ := hK.exists_forall_le' hd
    (fun z hz => L12Aux.volumeDensity_pos g a z (hKt hz))
  obtain ⟨C, _, hC⟩ := (hK.bddAbove_image hd).exists_ge 1
  refine ⟨c, max C 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  exact ⟨hlower z hz, (hC _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

/-- Integral transport follows from the original chart law with only the
smoothness needed to make its density measurable. -/
theorem lintegral_chart_volume (g : HermitianField M) (hg : MetricSmooth g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    (f : M.Carrier → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in (extChartAt (ComplexModel n) a).source, f y ∂μ =
      ∫⁻ z in chartTarget a, ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det) *
        f (chartInv a z) ∂lebesgueC n := by
  have ht : MeasurableSet (chartTarget a) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict (chartTarget a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((volumeDensity_continuousOn g hg a).aemeasurable ht)
  have hfg : AEMeasurable (fun z => f (L18Aux.chartInvExtension a z))
      ((lebesgueC n).restrict (chartTarget a)) :=
    (hf.comp (L18Aux.chartInvExtension_measurable a)).aemeasurable
  rw [L18Aux.riemannianVolume_restrict_eq_map g μ hμ a,
    lintegral_map hf (L18Aux.chartInvExtension_measurable a),
    lintegral_withDensity_eq_lintegral_mul₀ hd hfg]
  apply setLIntegral_congr_fun ht
  intro z hz
  simp only [Pi.mul_apply, L18Aux.chartInvExtension, ite_eq_left hz]

/-- Null assertions for the manifold volume pull back to Lebesgue measure
in every original chart. Positivity of the density, rather than an additional
geometric hypothesis, removes the weight. -/
theorem ae_chart_pullback (g : HermitianField M) (hg : MetricSmooth g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ) (a : M.Carrier)
    {P : M.Carrier → Prop}
    (hP : ∀ᵐ x ∂μ.restrict (extChartAt (ComplexModel n) a).source, P x) :
    ∀ᵐ z ∂(lebesgueC n).restrict (chartTarget a), P (chartInv a z) := by
  have ht := (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hd : AEMeasurable (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det))
      ((lebesgueC n).restrict (chartTarget a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((volumeDensity_continuousOn g hg a).aemeasurable ht)
  rw [L18Aux.riemannianVolume_restrict_eq_map g μ hμ a] at hP
  have hpull := ae_of_ae_map (L18Aux.chartInvExtension_measurable a).aemeasurable hP
  rw [ae_withDensity_iff' hd] at hpull
  filter_upwards [hpull, ae_restrict_mem ht] with z hz hzt
  have hpos : ENNReal.ofReal (Real.sqrt (realMetricFn g a z).det) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (L12Aux.volumeDensity_pos g a z hzt)).ne'
  simpa only [L18Aux.chartInvExtension, ite_eq_left hzt] using hz hpos

/-- The original smooth positive chart density makes the volume locally
finite, with no `SmoothMetric` structure. -/
theorem riemannianVolume_locallyFinite (g : HermitianField M) (hg : MetricSmooth g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ) : IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  let d : ComplexVector n → ℝ := fun z => Real.sqrt (realMetricFn g x z).det
  let z₀ : ComplexVector n := chartPt x x
  let B : ℝ := d z₀ + 1
  have hz₀ : z₀ ∈ chartTarget x := mem_extChartAt_target x
  have htarget : chartTarget x ∈ 𝓝 z₀ :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz₀
  have hd : ContinuousAt d z₀ :=
    (volumeDensity_continuousOn g hg x).continuousAt htarget
  have hB : {z | d z < B} ∈ 𝓝 z₀ :=
    hd.preimage_mem_nhds (Iio_mem_nhds (by dsimp [B]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hB)
  let s : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩
    chartPt x ⁻¹' Metric.ball z₀ ε
  have hs : IsOpen s :=
    isOpen_extChartAt_preimage' (I := ComplexModel n) x Metric.isOpen_ball
  have hxs : x ∈ s := ⟨mem_extChartAt_source x, Metric.mem_ball_self hε⟩
  refine ⟨s, hs.mem_nhds hxs, ?_⟩
  have hsource : s ⊆ (chartAt (ComplexVector n) x).source := by
    intro y hy
    simpa only [extChartAt_source] using hy.1
  rw [hμ x s hs.measurableSet hsource]
  have himage : chartPt x '' s ⊆ Metric.ball z₀ ε := by
    rintro z ⟨y, hy, rfl⟩
    exact hy.2
  have hmass : lebesgueC n (Metric.closedBall z₀ ε) < ⊤ := by
    rw [lebesgueC_eq_volume]
    exact (isCompact_closedBall z₀ ε).measure_lt_top
  calc
    ∫⁻ z in chartPt x '' s, ENNReal.ofReal (d z) ∂lebesgueC n
        ≤ ∫⁻ z in chartPt x '' s, ENNReal.ofReal B ∂lebesgueC n :=
      setLIntegral_mono measurable_const fun z hz =>
        ENNReal.ofReal_le_ofReal (hball (himage hz)).2.le
    _ = ENNReal.ofReal B * lebesgueC n (chartPt x '' s) := by simp
    _ ≤ ENNReal.ofReal B * lebesgueC n (Metric.closedBall z₀ ε) :=
      mul_le_mul_right (measure_mono
        (himage.trans Metric.ball_subset_closedBall)) (ENNReal.ofReal B)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass

end Yau.Proofs.D04AtlasGlueAux
