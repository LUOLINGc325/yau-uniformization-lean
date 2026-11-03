import Yau.LeafProofs.L19HeatRegularityDensityTest

/-! Actual Hilbert integration by parts for genuine compact chart tests. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual core-valued chart spacetime test path. -/
def scalarChartSpacetimeTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    ScalarEnergyDomain g μ hμ :=
  let ht := scalarChartTest_slice hφ t
  scalarEnergy_chartTest g μ hμ x ht.1 ht.2.1 (ht.2.2.trans hOt)

theorem scalarChartSpacetimeTestLp_eq_J (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    scalarChartSpacetimeTestLp g μ hμ x hOt hφ t =
      scalarEnergyL2 g μ hμ (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ) :=
  (scalarEnergyL2_coe g μ hμ _).symm

/-- The actual test path vanishes outside the time projection specified
by its genuine spacetime support. -/
theorem scalarChartSpacetimeTestLp_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) {t : ℝ} (ht : t ∉ I) :
    scalarChartSpacetimeTestLp g μ hμ x hOt hφ t = 0 := by
  have hz (z : ComplexVector n) : φ (z,t) = 0 := by
    by_contra hh
    exact ht (hφ.2.2 (subset_tsupport _ hh)).2
  apply Lp.ext
  filter_upwards [scalarChartSpacetimeTestLp_coe g μ hμ x hOt hφ t,Lp.coeFn_zero ℝ 2 μ] with y hy hy0
  rw [hy,hy0]
  simp only [chartPushforwardZero,hz,ite_self,Pi.zero_apply]

/-- Actual heat and actual L² chart tests satisfy Hilbert integration by
parts on every positive finite slab; the compact time support kills the
endpoint terms. -/
theorem scalarHeat_testPath_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (hlr : l < r)
    (f : Lp ℝ 2 μ) {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    (∫ t in Set.Ioo l r,
      inner ℝ (scalarHeatFamily g μ hμ t f)
        (scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t) +
      inner ℝ (scalarHeatFamily g μ hμ t f - scalarHeatInverse g μ hμ t f)
        (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t)) = 0 := by
  let S := fun t => scalarHeatFamily g μ hμ t f
  let H := fun t => scalarHeatFamily g μ hμ t f - scalarHeatInverse g μ hμ t f
  let ξ := scalarChartSpacetimeTestLp g μ hμ x hOt hφ
  let ξ' := scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ)
  have hd (t) (ht : t ∈ Set.Icc l r) :
      HasDerivAt (fun s => inner ℝ (S s) (ξ s))
        (inner ℝ (S t) (ξ' t) + inner ℝ (H t) (ξ t)) t :=
    (scalarHeatFamily_apply_hasDerivAt g μ hμ (hl.trans_le ht.1) f).inner ℝ
      (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt hφ t)
  have hH (t) (ht : t ∈ Set.Icc l r) : ContinuousAt H t :=
    (scalarHeatFamily_apply_hasDerivAt g μ hμ (hl.trans_le ht.1) f).continuousAt.sub
      ((ContinuousLinearMap.apply ℝ (Lp ℝ 2 μ) f).continuous.continuousAt.comp
        (scalarHeatInverse_continuousAt g μ hμ (hl.trans_le ht.1)))
  have hcont : ContinuousOn (fun t => inner ℝ (S t) (ξ' t) + inner ℝ (H t) (ξ t)) (Set.Icc l r) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact ((scalarHeatFamily_apply_hasDerivAt g μ hμ (hl.trans_le ht.1) f).continuousAt.inner
      (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t).continuousAt).add
      ((hH t ht).inner (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt hφ t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [Set.uIcc_of_le hlr.le] using ht))
    (hcont.intervalIntegrable_of_Icc hlr.le)
  have hlzero : ξ l = 0 := scalarChartSpacetimeTestLp_zero g μ hμ x hOt hφ (by simp)
  have hrzero : ξ r = 0 := scalarChartSpacetimeTestLp_zero g μ hμ x hOt hφ (by simp)
  rw [hlzero,hrzero,inner_zero_right,inner_zero_right,sub_self,
    intervalIntegral.integral_of_le hlr.le,integral_Ioc_eq_integral_Ioo] at hFTC
  exact hFTC

/-- The actual heat variational equation integrated against the genuine
moving chart test, with no assumed weak heat flow or test-path regularity. -/
theorem scalarHeat_testPath_energy_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (hlr : l < r)
    (f : Lp ℝ 2 μ) {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    (∫ t in Set.Ioo l r,
      -inner ℝ (scalarHeatFamily g μ hμ t f)
        (scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t) +
      scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f)
        (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ)) = 0 := by
  have hFTC := scalarHeat_testPath_integral g μ hμ x hOt hl hlr f hφ
  have heq : (fun t => -inner ℝ (scalarHeatFamily g μ hμ t f)
      (scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t) +
      scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f)
        (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ)) =ᵐ[volume.restrict (Set.Ioo l r)]
      (fun t => -(inner ℝ (scalarHeatFamily g μ hμ t f)
        (scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t) +
        inner ℝ (scalarHeatFamily g μ hμ t f - scalarHeatInverse g μ hμ t f)
          (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h := scalarHeatFamily_weak_equation g μ hμ (hl.trans ht.1) f
      (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ)
    rw [(scalarHeatFamily_apply_hasDerivAt g μ hμ (hl.trans ht.1) f).deriv,
      ← scalarChartSpacetimeTestLp_eq_J] at h
    linarith only [h]
  rw [integral_congr_ae heq,integral_neg,hFTC,neg_zero]

end Yau.LeafProofs.L19Aux
