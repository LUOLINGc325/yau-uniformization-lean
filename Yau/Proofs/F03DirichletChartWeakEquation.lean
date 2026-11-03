import Yau.Proofs.F03DirichletChartEnergy
import Yau.Proofs.F03DirichletChartTest
import Yau.LeafProofs.L19HeatRegularityWeakEquation

/-! Exact local weak PDE transport of the constructed supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
open LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The local PDE is derived from the actual supported variational heat
identity and the native computed metric-density identity. -/
theorem dirichletHeat_chartWeakEquation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (hOΩ : chartInv x '' O ⊆ Ω) {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 (μ.restrict Ω))
    {u : Parabolic.Point n → ℝ} {G : Parabolic.Point n → RIdx n → ℝ}
    (hu : MemLp u 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (Parabolic.productVolume O (Set.Ioo l r)))
    (hSlices : ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        ((fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))) ∧
        ∀ i, (fun z => G (z,t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt i (dirichletAmbientHeatEnergy g μ hμ Ω t f)) :
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
  have hEnergy := dirichletHeat_testPath_energy_integral g μ hμ Ω hΩ x (subset_closure.trans hOt) hOΩ hl hlr f hψ
  have hTslice := hI.1.prod_left_ae
  have hSslice := hI.2.prod_left_ae
  have hTime : (fun t => -inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
      (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) (L16Aux.test_timeDerivative hψ) t) +
      scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ)) =ᵐ[
      volume.restrict (Set.Ioo l r)] (fun t => ∫ z in O, F (z,t)) := by
    filter_upwards [hSlices,hTslice,hSslice] with t ht hT hS
    have hTimePair : inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) (L16Aux.test_timeDerivative hψ) t) =
        ∫ z in O, u (z,t) * deriv (fun s => φ (z,s)) t := by
      rw [scalarChartSpacetimeTestLp_inner g μ hμ x hO hOc hOt (L16Aux.test_timeDerivative hψ) t]
      apply integral_congr_ae
      filter_upwards [ht.1,ae_restrict_mem hO.measurableSet] with z hz hzO
      change Real.sqrt (realMetricFn g.form x z).det *
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) z *
        deriv (fun s => φ (z,s) / Real.sqrt (realMetricFn g.form x z).det) t = _
      rw [scalarChart_densityInverseTest_timeDerivative g x hφ.1 (z,t),← hz]
      field_simp [ne_of_gt (L12Aux.volumeDensity_pos g.form x z ((subset_closure.trans hOt) hzO))]
    have hEnergyPair : scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ) =
        ∫ z in O, scalarHeatChartSpatial g x G φ (z,t) := by
      let hs := scalarChartTest_slice hψ t
      have hEc := scalarClosedEnergy_chartTest g μ hμ x hO hOc hOt
        (dirichletAmbientHeatEnergy g μ hμ Ω t f) hs.1 hs.2.1 hs.2.2
      change scalarClosedEnergy g μ hμ (dirichletAmbientHeatEnergy g μ hμ Ω t f)
        (scalarChartSpacetimeTest g μ hμ x (subset_closure.trans hOt) hψ t : ScalarEnergySpace g μ hμ) = _ at hEc
      rw [hEc]
      apply integral_congr_ae
      have hGall := ae_all_iff.mpr (ht.2)
      filter_upwards [hGall,ae_restrict_mem hO.measurableSet] with z hz hzO
      change Real.sqrt (realMetricFn g.form x z).det *
        (∑ i, ∑ j, scalarHeatChartCoeff g x (z,t) i j *
          scalarEnergy_chartDerivativeCLM g μ hμ x hO hOc hOt j (dirichletAmbientHeatEnergy g μ hμ Ω t f) z *
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

/-- Genuine local energy and the exact homogeneous parabolic equation
are produced together, with actual slice identities for the same heat. -/
theorem dirichletHeat_chartWeakSolution (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (hOΩ : chartInv x '' O ⊆ Ω)
    {l r : ℝ} (hl : 0 < l) (hlr : l < r) (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃ (u : Parabolic.Point n → ℝ) (G : Parabolic.Point n → RIdx n → ℝ),
      Parabolic.LocalEnergy O (Set.Ioo l r) u G ∧
      Parabolic.WeakEquation O (Set.Ioo l r) (scalarHeatChartCoeff g x)
        (fun _ _ => 0) (fun _ => 0) u G ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo l r),
        (fun z => u (z,t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
            (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) := by
  obtain ⟨u,G,_huM,_hGM,hu,hG,hSlices⟩ :=
    dirichletHeat_chart_jointRepresentatives g μ hμ Ω hΩ x hO hOc hOt hl f
  have hlocal : Parabolic.LocalEnergy O (Set.Ioo l r) u G := by
    refine ⟨dirichletHeat_chart_jointWeakGradient g μ hμ Ω hΩ x hO hOc hOt hl f hu hG hSlices,?_⟩
    intro V c e _hV _hVC hVO hI
    have hm : Parabolic.productVolume V (Set.Ioo c e) ≤ Parabolic.productVolume O (Set.Ioo l r) :=
      Measure.prod_mono (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
        (Measure.restrict_mono (Set.Ioo_subset_Icc_self.trans hI) le_rfl)
    exact ⟨hu.mono_measure hm,fun i => (hG i).mono_measure hm⟩
  exact ⟨u,G,hlocal,dirichletHeat_chartWeakEquation g hK μ hμ Ω hΩ x hO hOc hOt hOΩ
    hl hlr f hu hG hSlices,hSlices.mono fun _ ht => ht.1⟩

end Yau.Proofs.F03Aux
