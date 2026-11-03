import Yau.Proofs.F03DirichletClassicalHeat
import Yau.Proofs.F03DirichletTestOperator
import Yau.LeafProofs.L19HeatRegularityChartPairing

/-! Actual continuous test pairing of the classical supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The actual zero-outside representative agrees in the original ambient
volume with actual L² zero extension of the same supported heat slice. -/
theorem dirichletClassicalHeat_ambient_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {t : ℝ} (ht : 0 < t) :
    (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) =ᵐ[μ]
      (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f) : M.Carrier → ℝ) := by
  have hi := (ae_eq_restrict_iff_indicator_ae_eq hΩ.measurableSet).mp
    (dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht)
  have he := extendL2_coe μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f)
  filter_upwards [hi,he] with y hy hz
  have hu : Ω.indicator (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) y =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f y t := by
    by_cases hyΩ : y ∈ Ω
    · exact Set.indicator_of_mem hyΩ _
    · rw [Set.indicator_of_notMem hyΩ,dirichletClassicalHeat_zero_outside g hK μ hμ Ω hΩ f y hyΩ]
  exact hu.symm.trans (hy.trans hz.symm)

/-- Genuine unweighted chart AE identity of every actual positive-time
classical representative, with no local continuity assumed across ∂Ω. -/
theorem dirichletClassicalHeat_chart_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (x : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOt : closure O ⊆ chartTarget x)
    {t : ℝ} (ht : 0 < t) :
    (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv x z) t) =ᵐ[volume.restrict O]
      scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
        (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f)) := by
  exact (scalarEnergy_chart_ae_eq g μ hμ x hO hOc hOt
    (dirichletClassicalHeat_ambient_ae g hK μ hμ Ω hΩ f ht)).trans
      (scalarEnergy_chartRestrictionCLM_coe g μ hμ x hO hOc hOt _).symm

/-- Each genuine Euclidean compact test of the actual classical heat has
an actual bounded linear source functional, fixed before the source f.
The inverse-density test is constructed by the proved native chart lemma. -/
theorem dirichletClassicalHeat_testOperator (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l)
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    dirichletChartTestOperator g μ hμ Ω hΩ.measurableSet x (subset_closure.trans hOt)
      (scalarChart_densityInverseTest g x (subset_closure.trans hOt) hφ) f =
      ∫ t in Set.Ioo l r, ∫ z in O,
        dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv x z) t * φ (z,t) := by
  let ψ : Parabolic.Point n → ℝ := fun p => φ p / Real.sqrt (realMetricFn g.form x p.1).det
  have hψ : Parabolic.Test (O ×ˢ Set.Ioo l r) ψ :=
    scalarChart_densityInverseTest g x (subset_closure.trans hOt) hφ
  rw [dirichletChartTestOperator_apply g μ hμ Ω hΩ.measurableSet x (subset_closure.trans hOt) hl hψ]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  change inner ℝ (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f))
    (scalarChartSpacetimeTestLp g μ hμ x (subset_closure.trans hOt) hψ t) =
    ∫ z in O, dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv x z) t * φ (z,t)
  rw [scalarChartSpacetimeTestLp_inner g μ hμ x hO hOc hOt hψ t]
  apply integral_congr_ae
  filter_upwards [dirichletClassicalHeat_chart_ae g hK μ hμ Ω hΩ f x hO hOc hOt
    (hl.trans ht.1),ae_restrict_mem hO.measurableSet] with z hz hzO
  change Real.sqrt (realMetricFn g.form x z).det *
    scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
      (l2ZeroExtension μ Ω hΩ.measurableSet (dirichletHeat g μ hμ Ω t f)) z *
        (φ (z,t) / Real.sqrt (realMetricFn g.form x z).det) = _
  rw [← hz]
  field_simp [ne_of_gt (LeafProofs.L12Aux.volumeDensity_pos g.form x z ((subset_closure.trans hOt) hzO))]

end Yau.Proofs.F03Aux
