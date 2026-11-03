import Yau.Proofs.F03DirichletAmbientEnergy
import Yau.LeafProofs.L19HeatRegularityTimeIntegration

/-! Genuine supported chart tests and integration of the actual variational equation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {n : ℕ} {M : ComplexManifold n}

/-- The sharp native support theorem makes the genuine chart test an
admissible member of the supported core. -/
def dirichletChartCoreTest (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    (hOΩ : chartInv x '' O ⊆ Ω) {η : ComplexVector n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O) :
    dirichletCore g μ hμ Ω :=
  ⟨scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans hOt),by
    apply (chartPushforwardZero_tsupport_subset x hcη (hηO.trans hOt)).trans
    exact (Set.image_mono hηO).trans hOΩ⟩

/-- The supported weak heat identity transported to the original ambient
energy space, preserving the actual zero extension and energy. -/
theorem dirichletHeat_ambient_weak_equation (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (μ.restrict Ω)) (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f -
      dirichletHeatInverse g μ hμ Ω t f)) (scalarEnergyL2 g μ hμ v.val) +
      scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f) v.val = 0 := by
  rw [← dirichletL2_zeroExtension g μ hμ Ω hΩ v,l2ZeroExtension_inner]
  change inner ℝ (dirichletHeat g μ hμ Ω t f - dirichletHeatInverse g μ hμ Ω t f)
    (dirichletL2 g μ hμ Ω v) + scalarClosedEnergy g μ hμ
      (dirichletHeatEnergy g μ hμ Ω t f).val v.val = 0
  rw [← dirichletClosedEnergy_eq_ambient g μ hμ Ω hΩ]
  have h := dirichletHeat_weak_equation g μ hμ Ω ht f v
  rw [(dirichletHeat_apply_hasDerivAt g μ hμ Ω ht f).deriv] at h
  exact h

/-- The fixed compact chart test is admissible at every time, including
its actual spatial support in Ω. -/
theorem dirichletHeat_chartSpacetimeTest_weak (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    (hOΩ : chartInv x '' O ⊆ Ω) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ)
    {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 (μ.restrict Ω)) :
    inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f -
      dirichletHeatInverse g μ hμ Ω t f))
      (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t) +
    scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
      (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ) = 0 := by
  let hs := scalarChartTest_slice hφ t
  let v := dirichletCoreToEnergy g μ hμ Ω
    (dirichletChartCoreTest g μ hμ Ω x hOt hOΩ hs.1 hs.2.1 hs.2.2)
  have h := dirichletHeat_ambient_weak_equation g μ hμ Ω hΩ ht f v
  rw [scalarChartSpacetimeTestLp_eq_J]
  exact h

/-- Hilbert integration by parts for the actual zero-extended supported
heat, with the endpoint terms killed by genuine compact time support. -/
theorem dirichletHeat_testPath_integral (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 (μ.restrict Ω))
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    (∫ t in Set.Ioo l r,
      inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x hOt (LeafProofs.L16Aux.test_timeDerivative hφ) t) +
      inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f -
        dirichletHeatInverse g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t)) = 0 := by
  let Z := l2ZeroExtension μ Ω hΩ
  let S := fun t => Z (dirichletHeat g μ hμ Ω t f)
  let H := fun t => Z (dirichletHeat g μ hμ Ω t f - dirichletHeatInverse g μ hμ Ω t f)
  let ξ := scalarChartSpacetimeTestLp g μ hμ x hOt hφ
  let ξ' := scalarChartSpacetimeTestLp g μ hμ x hOt (LeafProofs.L16Aux.test_timeDerivative hφ)
  have hdS (t) (ht : 0 < t) : HasDerivAt S (H t) t :=
    Z.hasFDerivAt.comp_hasDerivAt t (dirichletHeat_apply_hasDerivAt g μ hμ Ω ht f)
  have hd (t) (ht : t ∈ Set.Icc l r) :
      HasDerivAt (fun s => inner ℝ (S s) (ξ s))
        (inner ℝ (S t) (ξ' t) + inner ℝ (H t) (ξ t)) t :=
    (hdS t (hl.trans_le ht.1)).inner ℝ
      (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt hφ t)
  have hH (t) (ht : t ∈ Set.Icc l r) : ContinuousAt H t :=
    Z.continuous.continuousAt.comp
      ((dirichletHeat_apply_hasDerivAt g μ hμ Ω (hl.trans_le ht.1) f).continuousAt.sub
        ((ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ.restrict Ω)) f).continuous.continuousAt.comp
          (dirichletHeatInverse_continuousAt g μ hμ Ω (hl.trans_le ht.1))))
  have hcont : ContinuousOn (fun t => inner ℝ (S t) (ξ' t) + inner ℝ (H t) (ξ t)) (Set.Icc l r) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    exact ((hdS t (hl.trans_le ht.1)).continuousAt.inner
      (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt
        (LeafProofs.L16Aux.test_timeDerivative hφ) t).continuousAt).add
      ((hH t ht).inner (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt hφ t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [Set.uIcc_of_le hlr.le] using ht))
    (hcont.intervalIntegrable_of_Icc hlr.le)
  have hlzero : ξ l = 0 := scalarChartSpacetimeTestLp_zero g μ hμ x hOt hφ (by simp)
  have hrzero : ξ r = 0 := scalarChartSpacetimeTestLp_zero g μ hμ x hOt hφ (by simp)
  rw [hlzero,hrzero,inner_zero_right,inner_zero_right,sub_self,
    intervalIntegral.integral_of_le hlr.le,integral_Ioc_eq_integral_Ioo] at hFTC
  exact hFTC

/-- The actual supported variational equation integrated against the
admissible moving chart test. No desired local PDE is an input. -/
theorem dirichletHeat_testPath_energy_integral (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    (hOΩ : chartInv x '' O ⊆ Ω) {l r : ℝ} (hl : 0 < l) (hlr : l < r)
    (f : Lp ℝ 2 (μ.restrict Ω))
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    (∫ t in Set.Ioo l r,
      -inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x hOt (LeafProofs.L16Aux.test_timeDerivative hφ) t) +
      scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
        (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ)) = 0 := by
  have hFTC := dirichletHeat_testPath_integral g μ hμ Ω hΩ x hOt hl hlr f hφ
  have heq : (fun t => -inner ℝ
      (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
      (scalarChartSpacetimeTestLp g μ hμ x hOt (LeafProofs.L16Aux.test_timeDerivative hφ) t) +
      scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
        (scalarChartSpacetimeTest g μ hμ x hOt hφ t : ScalarEnergySpace g μ hμ)) =ᵐ[volume.restrict (Set.Ioo l r)]
      (fun t => -(inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x hOt (LeafProofs.L16Aux.test_timeDerivative hφ) t) +
        inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f -
          dirichletHeatInverse g μ hμ Ω t f)) (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have h := dirichletHeat_chartSpacetimeTest_weak g μ hμ Ω hΩ x hOt hOΩ hφ (hl.trans ht.1) f
    linarith only [h]
  rw [integral_congr_ae heq,integral_neg,hFTC,neg_zero]

end Yau.Proofs.F03Aux
