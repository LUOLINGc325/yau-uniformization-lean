import Yau.LeafProofs.L19HeatRegularityCoefficients

/-! The exact frozen weak parabolic equation of the actual scalar heat family. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The actual spatial divergence of the computed half inverse metric. -/
def scalarHeatChartDrift (g : SmoothMetric M) (x : M.Carrier)
    (p : Parabolic.Point n) (j : RIdx n) : ℝ :=
  ∑ i, Parabolic.d (fun z => scalarHeatChartCoeff g x (z,p.2) i j) p.1 i

theorem scalarHeatChartDrift_continuousOn (g : SmoothMetric M) (x : M.Carrier)
    (t : ℝ) (j : RIdx n) :
    ContinuousOn (fun z => scalarHeatChartDrift g x (z,t) j) (chartTarget x) := by
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact (rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
    (contDiffOn_const.mul (realMetricFn_inverse_contDiffOn g x i j)) i).continuousOn

/-- A genuinely continuous chart coefficient times a true compact
spacetime test belongs to the actual product L² space. -/
theorem scalarChart_coefficient_test_memLp (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {c : ComplexVector n → ℝ} (hc : ContinuousOn c (chartTarget x))
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) :
    MemLp (fun p => c p.1 * φ p) 2 (Parabolic.productVolume O I) := by
  have hcont : Continuous (fun p : Parabolic.Point n => φ p * c p.1) :=
    continuous_mul_of_continuousAt_tsupport hφ.1.continuous (fun p hp =>
      (hc.continuousAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (hOt (hφ.2.2 hp).1))).comp continuousAt_fst)
  have hm : MemLp (fun p : Parabolic.Point n => φ p * c p.1) 2 volume :=
    hcont.memLp_of_hasCompactSupport hφ.2.1.mul_right
  rw [L16Aux.productVolume_eq_restrict]
  convert hm.restrict (O ×ˢ I) using 1
  funext p
  ring

/-- The spatial integrand with exactly the frozen computed drift sign. -/
def scalarHeatChartSpatial (g : SmoothMetric M) (x : M.Carrier)
    (G : Parabolic.Point n → RIdx n → ℝ) (φ : Parabolic.Point n → ℝ)
    (p : Parabolic.Point n) : ℝ :=
  (∑ i, ∑ j, scalarHeatChartCoeff g x p i j * G p j *
    Parabolic.d (fun z => φ (z,p.2)) p.1 i) +
  ∑ j, scalarHeatChartDrift g x p j * G p j * φ p

/-- All terms in the actual weak equation are integrable, from the
constructed product L² values and gradients and genuine compact tests. -/
theorem scalarHeat_chartWeakIntegrands_integrable (g : SmoothMetric M) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {I : Set ℝ}
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O I))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O I))
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) :
    Integrable (fun p => u p * deriv (fun t => φ (p.1,t)) p.2) (Parabolic.productVolume O I) ∧
      Integrable (scalarHeatChartSpatial g x G φ) (Parabolic.productVolume O I) := by
  have hφt := L16Aux.test_timeDerivative hφ
  have hφtL : MemLp (fun p => deriv (fun t => φ (p.1,t)) p.2) 2 (Parabolic.productVolume O I) := by
    rw [L16Aux.productVolume_eq_restrict]
    exact (hφt.1.continuous.memLp_of_hasCompactSupport hφt.2.1).restrict _
  refine ⟨hu.integrable_mul hφtL,?_⟩
  have hflux (i j : RIdx n) : Integrable (fun p => scalarHeatChartCoeff g x p i j * G p j *
      Parabolic.d (fun z => φ (z,p.2)) p.1 i) (Parabolic.productVolume O I) := by
    have hc := ((contDiffOn_const (c := (1 / 2 : ℝ))).mul (realMetricFn_inverse_contDiffOn g x i j)).continuousOn
    have hm := scalarChart_coefficient_test_memLp x hOt hc (L16Aux.test_spatialDerivative hφ i)
    convert (hG j).integrable_mul hm using 1
    funext p
    dsimp only [Pi.mul_apply,scalarHeatChartCoeff]
    ring
  have hdrift (j : RIdx n) : Integrable (fun p => scalarHeatChartDrift g x p j * G p j * φ p)
      (Parabolic.productVolume O I) := by
    have hc := scalarHeatChartDrift_continuousOn g x 0 j
    have hm := scalarChart_coefficient_test_memLp x hOt hc hφ
    convert (hG j).integrable_mul hm using 1
    funext p
    dsimp only [Pi.mul_apply,scalarHeatChartDrift,scalarHeatChartCoeff,Parabolic.d]
    ring
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hflux i j))).add
      (integrable_finsetSum Finset.univ (fun j _ => hdrift j))

/-- The internally constructed heat chart representatives satisfy the
exact frozen nondivergence weak equation with the actual half inverse
metric and zero drift coefficient. -/
theorem scalarHeat_chartWeakEquation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 μ)
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f)) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (scalarHeatEnergy g μ hμ t f)) :
    Parabolic.WeakEquation O (Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) (fun _ => 0) u G := by
  intro φ hφ
  let ψ : Parabolic.Point n → ℝ := fun p => φ p / Real.sqrt (realMetricFn g.form x p.1).det
  have hψ : Parabolic.Test (O ×ˢ Set.Ioo l r) ψ :=
    scalarChart_densityInverseTest g x (subset_closure.trans hOt) hφ
  have hI := scalarHeat_chartWeakIntegrands_integrable g x (subset_closure.trans hOt) hu hG hφ
  let F : Parabolic.Point n → ℝ := fun p => -(u p * deriv (fun t => φ (p.1,t)) p.2) +
    scalarHeatChartSpatial g x G φ p
  have hF : Integrable F (Parabolic.productVolume O (Set.Ioo l r)) := by
    simpa only [F,Pi.add_def,Pi.neg_def] using hI.1.neg.add hI.2
  have hEnergy := scalarHeat_testPath_energy_integral g μ hμ x (subset_closure.trans hOt) hl hlr f hψ
  have hTslice := hI.1.prod_left_ae
  have hSslice := hI.2.prod_left_ae
  have hTime : (fun t => -inner ℝ (scalarHeatFamily g μ hμ t f)
      (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) (L16Aux.test_timeDerivative hψ) t) +
      scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ)) =ᵐ[
      volume.restrict (Set.Ioo l r)] (fun t => ∫ z in O, F (z,t)) := by
    filter_upwards [hSlices,hTslice,hSslice] with t ht hT hS
    have hTimePair : inner ℝ (scalarHeatFamily g μ hμ t f)
        (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) (L16Aux.test_timeDerivative hψ) t) =
        ∫ z in O, u (z,t) * deriv (fun s => φ (z,s)) t := by
      rw [scalarChartSpacetimeTestLp_inner g μ hμ x hO hOc hOt (L16Aux.test_timeDerivative hψ) t]
      apply integral_congr_ae
      filter_upwards [ht.1,ae_restrict_mem hO.measurableSet] with z hz hzO
      change Real.sqrt (realMetricFn g.form x z).det *
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f) z *
        deriv (fun s => φ (z,s) / Real.sqrt (realMetricFn g.form x z).det) t = _
      rw [scalarChart_densityInverseTest_timeDerivative g x hφ.1 (z,t),← hz]
      field_simp [ne_of_gt (L12Aux.volumeDensity_pos g.form x z ((subset_closure.trans hOt) hzO))]
    have hEnergyPair : scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ) =
        ∫ z in O, scalarHeatChartSpatial g x G φ (z,t) := by
      let hs := scalarChartTest_slice hψ t
      have hEc := scalarClosedEnergy_chartTest g μ hμ x hO hOc hOt
        (scalarHeatEnergy g μ hμ t f) hs.1 hs.2.1 hs.2.2
      change scalarClosedEnergy g μ hμ (scalarHeatEnergy g μ hμ t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ) = _ at hEc
      rw [hEc]
      apply integral_congr_ae
      have hGall := ae_all_iff.mpr (ht.2)
      filter_upwards [hGall,ae_restrict_mem hO.measurableSet] with z hz hzO
      change Real.sqrt (realMetricFn g.form x z).det *
        (∑ i, ∑ j, scalarHeatChartCoeff g x (z,t) i j *
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j (scalarHeatEnergy g μ hμ t f) z *
          rDeriv (fun w => φ (w,t) / Real.sqrt (realMetricFn g.form x w).det) z i) = _
      simp_rw [← hz]
      exact scalarHeatChartCoeff_density_test g hK x ((subset_closure.trans hOt) hzO) t
        ((hφ.1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) z) (fun j => G (z,t) j)
    rw [hTimePair,hEnergyPair]
    change -(∫ z in O, u (z,t) * deriv (fun s => φ (z,s)) t) +
      (∫ z in O, scalarHeatChartSpatial g x G φ (z,t)) =
      ∫ z in O, -(u (z,t) * deriv (fun s => φ (z,s)) t) + scalarHeatChartSpatial g x G φ (z,t)
    have hAdd := integral_add hT.neg hS
    simp only [Pi.neg_def] at hAdd
    rw [hAdd,integral_neg]
  have hActual : (∫ p, F p ∂Parabolic.productVolume O (Set.Ioo l r)) = 0 := by
    change (∫ p, F p ∂(volume.restrict O).prod (volume.restrict (Set.Ioo l r))) = 0
    rw [integral_prod_symm _ hF,← integral_congr_ae hTime]
    exact hEnergy
  simp only [zero_mul,integral_zero]
  convert hActual using 1
  congr 1
  funext p
  simp only [F,scalarHeatChartSpatial,scalarHeatChartDrift,zero_sub,neg_mul,
    Finset.sum_neg_distrib,sub_neg_eq_add]
  ring

/-- The actual heat construction internally supplies the full frozen
local weak solution, including its genuine local energy and exact weak
heat equation, on every positive relatively compact chart cylinder. -/
theorem scalarHeat_chartWeakSolution (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 μ) :
    ∃ (u : Parabolic.Point n → ℝ) (G : Parabolic.Point n → RIdx n → ℝ),
      Parabolic.LocalEnergy O (Set.Ioo l r) u G ∧
      Parabolic.WeakEquation O (Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) (fun _ => 0) u G ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        (fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (scalarHeatFamily g μ hμ t f) := by
  obtain ⟨u,G,_huM,_hGM,hu,hG,hSlices⟩ :=
    scalarHeat_chart_jointRepresentatives g μ hμ x hO hOc hOt hl f
  have hlocal : Parabolic.LocalEnergy O (Set.Ioo l r) u G := by
    refine ⟨scalarHeat_chart_jointWeakGradient g μ hμ x hO hOc hOt hl f hu hG hSlices,?_⟩
    intro V c e _hV _hVC hVO hI
    have hm : Parabolic.productVolume V (Set.Ioo c e) ≤ Parabolic.productVolume O (Set.Ioo l r) :=
      Measure.prod_mono (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
        (Measure.restrict_mono (Set.Ioo_subset_Icc_self.trans hI) le_rfl)
    exact ⟨hu.mono_measure hm,fun i => (hG i).mono_measure hm⟩
  exact ⟨u,G,hlocal,scalarHeat_chartWeakEquation g hK μ hμ x hO hOc hOt hl hlr f hu hG hSlices,
    hSlices.mono fun _ ht => ht.1⟩

end Yau.LeafProofs.L19Aux
