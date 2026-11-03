import Yau.LeafProofs.L19HeatRegularityLpDifferentiation
import Yau.LeafProofs.L16EnergyEquation

/-! Genuine density-corrected spacetime tests on actual metric charts. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Division by the actual positive metric density preserves a true
compact spacetime test. Smoothness outside the chart follows from its
actual compact support, not a global inverse-density premise. -/
theorem scalarChart_densityInverseTest (g : SmoothMetric M) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) :
    Parabolic.Test (O ×ˢ I)
      (fun p => φ p / Real.sqrt (realMetricFn g.form x p.1).det) := by
  refine ⟨?_,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport φ
    · have hz : p.1 ∈ chartTarget x := hOt (hφ.2.2 hp).1
      have hρ : ContDiffAt ℝ ∞ (fun z => Real.sqrt (realMetricFn g.form x z).det) p.1 :=
        (volumeDensity_contDiffOn g x).contDiffAt
          ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
      exact hφ.1.contDiffAt.div (hρ.comp p contDiffAt_fst)
        (ne_of_gt (L12Aux.volumeDensity_pos g.form x p.1 hz))
    · have heq : (fun p => φ p / Real.sqrt (realMetricFn g.form x p.1).det) =ᶠ[𝓝 p]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
        change φ q = 0 at hq
        simp only [hq,zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · change HasCompactSupport (fun p => φ p * (Real.sqrt (realMetricFn g.form x p.1).det)⁻¹)
    exact hφ.2.1.mul_right
  · exact (tsupport_mul_subset_left :
      tsupport (fun p => φ p / Real.sqrt (realMetricFn g.form x p.1).det) ⊆ tsupport φ).trans hφ.2.2

/-- The actual time derivative of the density-corrected test is just the
original time derivative divided by that same time-independent density. -/
theorem scalarChart_densityInverseTest_timeDerivative (g : SmoothMetric M) (x : M.Carrier)
    {φ : Parabolic.Point n → ℝ} (hφ : ContDiff ℝ ∞ φ) (p : Parabolic.Point n) :
    deriv (fun t => φ (p.1,t) / Real.sqrt (realMetricFn g.form x p.1).det) p.2 =
      deriv (fun t => φ (p.1,t)) p.2 / Real.sqrt (realMetricFn g.form x p.1).det := by
  exact (((hφ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2).hasDerivAt.div_const
    (Real.sqrt (realMetricFn g.form x p.1).det)).deriv

/-- A fixed true spacetime test gives an actual manifold L²-valued test
path by the already constructed global chart pushforward. -/
def scalarChartSpacetimeTestLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) : Lp ℝ 2 μ :=
  let ht := scalarChartTest_slice hφ t
  scalarEnergyDomainL2 g μ hμ (scalarEnergy_chartTest g μ hμ x ht.1 ht.2.1 (ht.2.2.trans hOt))

theorem scalarChartSpacetimeTestLp_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    scalarChartSpacetimeTestLp g μ hμ x hOt hφ t =ᵐ[μ]
      chartPushforwardZero x (fun z => φ (z,t)) :=
  scalarEnergyDomainL2_coe g μ hμ _

/-- A true compact spacetime chart test differentiates in the actual
manifold L² norm. The proof constructs a common compact support, a genuine
L² difference-quotient dominator, and uses scalar dominated convergence. -/
theorem scalarChartSpacetimeTestLp_hasDerivAt (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    HasDerivAt (scalarChartSpacetimeTestLp g μ hμ x hOt hφ)
      (scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t) t := by
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  let φ' : Parabolic.Point n → ℝ := fun p => deriv (fun s => φ (p.1,s)) p.2
  have hφ' : Parabolic.Test (O ×ˢ I) φ' := L16Aux.test_timeDerivative hφ
  let F := fun s => chartPushforwardZero x (fun z => φ (z,s))
  let F' := fun s => chartPushforwardZero x (fun z => φ' (z,s))
  have hF (s) : MemLp (F s) 2 μ := by
    let hs := scalarChartTest_slice hφ s
    exact scalarEnergyDomain_memLp g μ hμ (scalarEnergy_chartTest g μ hμ x hs.1 hs.2.1 (hs.2.2.trans hOt))
  have hF' (s) : MemLp (F' s) 2 μ := by
    let hs := scalarChartTest_slice hφ' s
    exact scalarEnergyDomain_memLp g μ hμ (scalarEnergy_chartTest g μ hμ x hs.1 hs.2.1 (hs.2.2.trans hOt))
  have hd (s : ℝ) (y : M.Carrier) : HasDerivAt (fun r => F r y) (F' s y) s := by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · have hh := ((hφ.1.comp ((contDiff_const (c := chartPt x y)).prodMk contDiff_id)).differentiable (by simp) s).hasDerivAt
      simpa only [Function.comp_def,id_eq,F,F',φ',chartPushforwardZero,ite_eq_left hy] using hh
    · simpa only [F,F',chartPushforwardZero,ite_eq_right hy] using hasDerivAt_const s (0 : ℝ)
  obtain ⟨c,hc⟩ := hφ'.1.continuous.norm.bddAbove_range_of_hasCompactSupport hφ'.2.1.norm
  let C := max c 0
  have hC : 0 ≤ C := le_max_right _ _
  have hFbound (s : ℝ) (y : M.Carrier) : ‖F' s y‖ ≤ C := by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · change ‖chartPushforwardZero x (fun z => φ' (z,s)) y‖ ≤ C
      simp only [chartPushforwardZero,ite_eq_left hy]
      exact (hc ⟨(chartPt x y,s),rfl⟩).trans (le_max_left _ _)
    · simpa only [F',chartPushforwardZero,ite_eq_right hy,norm_zero] using hC
  let Kc := Prod.fst '' tsupport φ
  have hKc : IsCompact Kc := hφ.2.1.image continuous_fst
  have hKct : Kc ⊆ chartTarget x := by
    rintro z ⟨p,hp,rfl⟩
    exact hOt (hφ.2.2 hp).1
  let K := chartInv x '' Kc
  have hK : IsCompact K := hKc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hKct)
  have hzero (s : ℝ) {y : M.Carrier} (hyK : y ∉ K) : F s y = 0 := by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · have hp : (chartPt x y,s) ∉ tsupport φ := by
        intro hp
        apply hyK
        refine ⟨chartPt x y,⟨(chartPt x y,s),hp,rfl⟩,?_⟩
        exact (extChartAt (ComplexModel n) x).left_inv hy
      simp only [F,chartPushforwardZero,ite_eq_left hy,image_eq_zero_of_notMem_tsupport hp]
    · simp only [F,chartPushforwardZero,ite_eq_right hy]
  let B : M.Carrier → ℝ := K.indicator (fun _ => C)
  have hB : MemLp B 2 μ := memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet C
    (Or.inr hK.measure_lt_top.ne)
  have hquot : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ y ∂μ, ‖(s-t)⁻¹ * (F s y - F t y)‖ ≤ B y := by
    apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    by_cases hyK : y ∈ K
    · simp only [B,Set.indicator_of_mem hyK]
      by_cases hst : s = t
      · simp only [hst,sub_self,inv_zero,zero_mul,norm_zero]
        exact hC
      · have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun r (_hr : r ∈ (Set.univ : Set ℝ)) => (hd r y).hasDerivWithinAt)
          (fun r (_hr : r ∈ (Set.univ : Set ℝ)) => hFbound r y)
          convex_univ (Set.mem_univ t) (Set.mem_univ s)
        rw [norm_mul,norm_inv]
        calc
          _ ≤ ‖s-t‖⁻¹ * (C * ‖s-t‖) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))
          _ = C := by rw [mul_left_comm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hst)),mul_one]
    · simp only [hzero s hyK,hzero t hyK,sub_self,mul_zero,norm_zero,B,Set.indicator_of_notMem hyK,le_refl]
  have hderiv := scalarL2_hasDerivAt_of_dominated hF (hF' t) hB t
    (ae_of_all _ (hd t)) hquot
  have hpath : (fun s => (hF s).toLp (F s)) = scalarChartSpacetimeTestLp g μ hμ x hOt hφ := by
    funext s
    apply Lp.ext
    exact (hF s).coeFn_toLp.trans (scalarChartSpacetimeTestLp_coe g μ hμ x hOt hφ s).symm
  have htarget : (hF' t).toLp (F' t) =
      scalarChartSpacetimeTestLp g μ hμ x hOt (L16Aux.test_timeDerivative hφ) t := by
    apply Lp.ext
    exact (hF' t).coeFn_toLp.trans
      (scalarChartSpacetimeTestLp_coe g μ hμ x hOt hφ' t).symm
  rw [hpath,htarget] at hderiv
  exact hderiv

end Yau.LeafProofs.L19Aux
