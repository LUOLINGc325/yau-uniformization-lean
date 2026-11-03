import Yau.LeafProofs.L19HeatRegularityTimeIntegration

/-! Exact chart transport of actual L² pairings against genuine chart tests. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- An arbitrary actual L² vector paired with a genuine global chart test
has exactly the computed chart density and the actual restricted L² vector. -/
theorem scalarEnergyL2_chartTest_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (f : Lp ℝ 2 μ)
    {η : ComplexVector n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηO : tsupport η ⊆ O) :
    inner ℝ f (scalarEnergyDomainL2 g μ hμ
      (scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans (subset_closure.trans hOt)))) =
      ∫ z in O, Real.sqrt (realMetricFn g.form x z).det *
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt f z * η z := by
  let k := scalarEnergy_chartTest g μ hμ x hη hcη (hηO.trans (subset_closure.trans hOt))
  let ψ : M.Carrier → ℝ := k
  have hψM : AEStronglyMeasurable ψ μ := (continuous_of_smoothFn k.2.1).aestronglyMeasurable
  have hI : inner ℝ f (scalarEnergyDomainL2 g μ hμ k) = ∫ y, f y * ψ y ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarEnergyDomainL2_coe g μ hμ k] with y hy
    rw [hy]
    simp only [ψ,RCLike.inner_apply,conj_trivial,mul_comm]
  have hsource : (∫ y, f y * ψ y ∂μ) =
      ∫ y in (extChartAt (ComplexModel n) x).source, f y * ψ y ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    change f y * chartPushforwardZero x η y = 0
    simp only [chartPushforwardZero,ite_eq_right hy,mul_zero]
  have htransport := integral_chart_volume_ae g μ hμ x
    ((Lp.aestronglyMeasurable f).mul hψM).restrict
  rw [lebesgueC_eq_volume] at htransport
  simp only [Pi.mul_apply,smul_eq_mul] at htransport
  have htest {z : ComplexVector n} (hz : z ∈ chartTarget x) : ψ (chartInv x z) = η z :=
    chartPushforwardZero_chartInv x η hz
  have hlocal : (∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
      (f (chartInv x z) * ψ (chartInv x z))) =
      ∫ z in O, Real.sqrt (realMetricFn g.form x z).det * (f (chartInv x z) * η z) := by
    calc
      _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
          (f (chartInv x z) * η z) := by
        apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
        intro z hz
        change Real.sqrt (realMetricFn g.form x z).det * (f (chartInv x z) * ψ (chartInv x z)) = _
        rw [htest hz]
      _ = _ := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet (subset_closure.trans hOt)
        intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz.2 (hηO hh)),mul_zero,mul_zero]
  rw [hI,hsource,htransport,hlocal]
  apply integral_congr_ae
  filter_upwards [scalarEnergy_chartRestrictionCLM_coe g μ hμ x hO hOc hOt f] with z hz
  rw [hz]
  ring

/-- Actual L² spacetime-test pairing in its actual local chart. -/
theorem scalarChartSpacetimeTestLp_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) (f : Lp ℝ 2 μ) :
    inner ℝ f (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) hφ t) =
      ∫ z in O, Real.sqrt (realMetricFn g.form x z).det *
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt f z * φ (z,t) := by
  let ht := scalarChartTest_slice hφ t
  exact scalarEnergyL2_chartTest_inner g μ hμ x hO hOc hOt f ht.1 ht.2.1 ht.2.2

end Yau.LeafProofs.L19Aux
