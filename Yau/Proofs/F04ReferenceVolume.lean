import Yau.Proofs.F04Source

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L18Aux
open Yau.LeafProofs (metricDensityRatio)

variable {n : ℕ} {M : ComplexManifold n}

/-- A reference volume constructs the genuine volume of every smooth
Hermitian field, including an incomplete evolving metric. -/
theorem isRiemannianVolume_from_reference
    (g : SmoothMetric M) (h : HermitianField M) (hh : MetricSmooth h)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) :
    IsRiemannianVolume h
      (μ.withDensity (fun x => ENNReal.ofReal (metricDensityRatio h g.form x))) := by
  have hr : Measurable (fun x => ENNReal.ofReal (metricDensityRatio h g.form x)) :=
    (ENNReal.continuous_ofReal.comp (Yau.LeafProofs.metricDensityRatio_continuous h g.form hh
      (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g))).measurable
  intro a s hs hsa
  have hsub : s ⊆ (extChartAt (ComplexModel n) a).source := by
    simpa only [extChartAt_source] using hsa
  have ht := (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
  have hp := (chartInvExtension_measurable a) hs
  calc
    (μ.withDensity (fun x => ENNReal.ofReal (metricDensityRatio h g.form x))) s =
        ∫⁻ x in (extChartAt (ComplexModel n) a).source,
          s.indicator (fun x => ENNReal.ofReal (metricDensityRatio h g.form x)) x ∂μ := by
      rw [withDensity_apply _ hs, lintegral_indicator hs, Measure.restrict_restrict hs,
        inter_eq_left.mpr hsub]
    _ = ∫⁻ z in chartTarget a, ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) *
        s.indicator (fun x => ENNReal.ofReal (metricDensityRatio h g.form x)) (chartInv a z)
          ∂lebesgueC n := lintegral_chart_volume g μ hμ a _ (hr.indicator hs)
    _ = ∫⁻ z in chartTarget a, (chartInvExtension a ⁻¹' s).indicator
        (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det)) z ∂lebesgueC n := by
      apply setLIntegral_congr_fun ht
      intro z hz
      change z ∈ chartTarget a at hz
      change ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) *
        s.indicator (fun x => ENNReal.ofReal (metricDensityRatio h g.form x)) (chartInv a z) =
        (chartInvExtension a ⁻¹' s).indicator
          (fun z => ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det)) z
      have hpred : z ∈ chartInvExtension a ⁻¹' s ↔ chartInv a z ∈ s := by
        change chartInvExtension a z ∈ s ↔ chartInv a z ∈ s
        rw [chartInvExtension, ite_eq_left hz]
      by_cases hzs : chartInv a z ∈ s
      · rw [indicator_of_mem hzs, indicator_of_mem (hpred.mpr hzs)]
        exact Yau.LeafProofs.metricDensityRatio_mul_volumeDensity h g.form a z hz
      · rw [indicator_of_notMem hzs,
          indicator_of_notMem (fun hmem => hzs (hpred.mp hmem)), mul_zero]
    _ = ∫⁻ z in chartInvExtension a ⁻¹' s ∩ chartTarget a,
        ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det) ∂lebesgueC n := by
      rw [lintegral_indicator hp, Measure.restrict_restrict hp]
    _ = ∫⁻ z in chartPt a '' s,
        ENNReal.ofReal (Real.sqrt (realMetricFn h a z).det) ∂lebesgueC n := by
      rw [← chart_image_eq_extension_preimage, inter_eq_left.mpr hsub]

end Yau.F04Proof
