import Yau.Proofs.F04SupportedL2Pairing
import Yau.Proofs.F04ChartEnergyTest
import Yau.LeafProofs.L19HeatRegularityChartPairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.Proofs.F03Aux Yau.LeafProofs.L19Aux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual supported pivot pairing with the genuine density-corrected
 chart test is exactly the Euclidean chart pairing. This applies both to
 the original continuous trace and to the actual source pivot vector. -/
theorem supportedL2_chartDensityTest_inner
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (c : M.Carrier) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (t : ℝ) (f : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ f (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap
        (scalarChart_densityInverseTest g c (subset_closure.trans hOt) hφ) t))) =
      ∫ z in O, scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ f) z * φ (z, t) := by
  let θ : Point n → ℝ := fun p => φ p / Real.sqrt (realMetricFn g.form c p.1).det
  have hθ : Test (O ×ˢ I) θ := scalarChart_densityInverseTest g c (subset_closure.trans hOt) hφ
  have hSlice := scalarChartTest_slice hθ t
  let k := chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap hθ t
  change inner ℝ f (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω k)) = _
  rw [supportedL2_core_pairing g μ hμ Ω hΩ f k]
  change inner ℝ (l2ZeroExtension μ Ω hΩ f) (scalarEnergyDomainL2 g μ hμ
    (scalarEnergy_chartTest g μ hμ c hSlice.1 hSlice.2.1 (hSlice.2.2.trans (subset_closure.trans hOt)))) = _
  rw [scalarEnergyL2_chartTest_inner g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ f)
    hSlice.1 hSlice.2.1 hSlice.2.2]
  apply setIntegral_congr_fun hO.measurableSet
  intro z hz
  change Real.sqrt (realMetricFn g.form c z).det *
    scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ f) z *
    (φ (z, t) / Real.sqrt (realMetricFn g.form c z).det) = _
  field_simp [ne_of_gt (Yau.LeafProofs.L12Aux.volumeDensity_pos g.form c z (hOt (subset_closure hz)))]

/-- The actual density correction is independent of time, so the genuine
 supported time-derivative core is exactly the corrected original test's
 time derivative. The equality is at the compact core, before completion. -/
theorem chartSupportedTestCore_density_timeDerivative
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (c : M.Carrier) {O : Set (Space n)}
    (hOt : O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) {I : Set ℝ}
    {φ : Point n → ℝ} (hφ : Test (O ×ˢ I) φ) (t : ℝ) :
    chartSupportedTestCore g μ hμ Ω c hOt hMap
      (Yau.LeafProofs.L16Aux.test_timeDerivative (scalarChart_densityInverseTest g c hOt hφ)) t =
    chartSupportedTestCore g μ hμ Ω c hOt hMap
      (scalarChart_densityInverseTest g c hOt (Yau.LeafProofs.L16Aux.test_timeDerivative hφ)) t := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ (extChartAt (ComplexModel n) c).source
  · change chartPushforwardZero c
      (fun z => deriv (fun s => φ (z, s) / Real.sqrt (realMetricFn g.form c z).det) t) y =
      chartPushforwardZero c
        (fun z => deriv (fun s => φ (z, s)) t / Real.sqrt (realMetricFn g.form c z).det) y
    simp only [chartPushforwardZero, ite_eq_left hy]
    exact scalarChart_densityInverseTest_timeDerivative g c hφ.1 (chartPt c y, t)
  · change chartPushforwardZero c
      (fun z => deriv (fun s => φ (z, s) / Real.sqrt (realMetricFn g.form c z).det) t) y =
      chartPushforwardZero c
        (fun z => deriv (fun s => φ (z, s)) t / Real.sqrt (realMetricFn g.form c z).det) y
    simp only [chartPushforwardZero, ite_eq_right hy]

end Yau.F04Proof
