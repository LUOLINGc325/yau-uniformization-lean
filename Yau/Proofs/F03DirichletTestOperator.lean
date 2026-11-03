import Yau.Proofs.F03DirichletChartTest

/-! Actual bounded test functionals for the later finite jet closed graph. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- A genuine chart test paired with the actual supported heat, as an
operator before all source vectors. -/
def dirichletChartPairingPath (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    {I : Set ℝ} {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ) (t : ℝ) :
    Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ :=
  (innerSL ℝ (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t)).comp
    ((l2ZeroExtension μ Ω hΩ).comp (dirichletHeat g μ hμ Ω t))

theorem dirichletChartPairingPath_continuousAt (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    {I : Set ℝ} {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ I) φ)
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt (dirichletChartPairingPath g μ hμ Ω hΩ x hOt hφ) t := by
  have hξ := (scalarChartSpacetimeTestLp_hasDerivAt g μ hμ x hOt hφ t).continuousAt
  have hS := (dirichletHeat_hasDerivAt g μ hμ Ω ht).continuousAt
  change ContinuousAt (fun s => (innerSL ℝ (scalarChartSpacetimeTestLp g μ hμ x hOt hφ s)).comp
    ((l2ZeroExtension μ Ω hΩ).comp (dirichletHeat g μ hμ Ω s))) t
  exact ((innerSL ℝ).continuous.continuousAt.comp hξ).clm_comp
    (continuousAt_const.clm_comp hS)

/-- Actual operator-norm continuity gives a Bochner-integrable operator
path on every fixed positive compact slab. -/
theorem dirichletChartPairingPath_integrable (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {l r : ℝ} (hl : 0 < l)
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    IntegrableOn (dirichletChartPairingPath g μ hμ Ω hΩ x hOt hφ) (Set.Ioo l r) := by
  have hc : ContinuousOn (dirichletChartPairingPath g μ hμ Ω hΩ x hOt hφ) (Set.Icc l r) :=
    fun t ht => (dirichletChartPairingPath_continuousAt g μ hμ Ω hΩ x hOt hφ
      (hl.trans_le ht.1)).continuousWithinAt
  exact (hc.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self

/-- This actual bounded functional is defined before every initial source.
Higher jet tests will move their derivatives onto this fixed smooth test. -/
def dirichletChartTestOperator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) {l r : ℝ}
    {φ : Parabolic.Point n → ℝ} (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) :
    Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ :=
  ∫ t in Set.Ioo l r, dirichletChartPairingPath g μ hμ Ω hΩ x hOt hφ t

/-- Exact evaluation of the genuine bounded operator is the original
heat pairing integral, not a chosen scalar representation. -/
theorem dirichletChartTestOperator_apply (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    {l r : ℝ} (hl : 0 < l) {φ : Parabolic.Point n → ℝ}
    (hφ : Parabolic.Test (O ×ˢ Set.Ioo l r) φ) (f : Lp ℝ 2 (μ.restrict Ω)) :
    dirichletChartTestOperator g μ hμ Ω hΩ x hOt hφ f =
      ∫ t in Set.Ioo l r, inner ℝ (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
        (scalarChartSpacetimeTestLp g μ hμ x hOt hφ t) := by
  unfold dirichletChartTestOperator
  rw [ContinuousLinearMap.integral_apply (dirichletChartPairingPath_integrable g μ hμ Ω hΩ x hOt hl hφ)]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [dirichletChartPairingPath,ContinuousLinearMap.comp_apply,innerSL_apply_apply]
  exact real_inner_comm _ _

end Yau.Proofs.F03Aux
