import Yau.Proofs.F03DirichletChartWeakEquation
import Yau.LeafProofs.L19HeatRegularityInterior

/-! Native interior smoothing and every-time representatives of supported heat. -/
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

/-- The smooth local representative agrees with the constructed actual
heat at every time, by the two genuine continuous L² paths. -/
theorem dirichletHeat_chart_smoothSlice_every_time (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω) (x : M.Carrier)
    {O V : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget x) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {l r : ℝ} (hl : 0 < l) (f : Lp ℝ 2 (μ.restrict Ω))
    {v : Parabolic.Point n → ℝ} (hv : ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r))
    (hAE : ∀ᵐ t ∂volume.restrict (Set.Ioo l r), (fun z => v (z,t)) =ᵐ[volume.restrict O]
      scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))) :
    ∀ t ∈ Set.Ioo l r, (fun z => v (z,t)) =ᵐ[volume.restrict V]
      (fun z => (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) (chartInv x z)) := by
  obtain ⟨A,hAc,hA⟩ := scalarSmoothSlice_exists_continuousLp hO hV hVc hVO hv
  let R := scalarEnergy_chartRestrictionCLM g μ hμ x hV hVc
    (hVO.trans (subset_closure.trans hOt))
  let B := fun t => R (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
  have hBc : ContinuousOn B (Set.Ioo l r) := fun t ht =>
    ((scalarEnergy_chartRestrictionCLM g μ hμ x hV hVc
      (hVO.trans (subset_closure.trans hOt))).continuous.continuousAt.comp
      ((l2ZeroExtension μ Ω hΩ).continuous.continuousAt.comp
        (dirichletHeat_apply_hasDerivAt g μ hμ Ω (hl.trans ht.1) f).continuousAt)).continuousWithinAt
  have hAB : A =ᵐ[volume.restrict (Set.Ioo l r)] B := by
    filter_upwards [hAE,ae_restrict_mem measurableSet_Ioo] with t ht htI
    apply Lp.ext
    have hOV : V ⊆ O := subset_closure.trans hVO
    have hvO := ae_restrict_of_ae_restrict_of_subset hOV ht
    have hOuter := ae_restrict_of_ae_restrict_of_subset hOV
      (scalarEnergy_chartRestrictionCLM_coe g μ hμ x hO hOc hOt (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)))
    have hInner := scalarEnergy_chartRestrictionCLM_coe g μ hμ x hV hVc
      (hVO.trans (subset_closure.trans hOt)) (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))
    filter_upwards [hA t htI,hvO,hOuter,hInner] with z hAz hvz hoz hiz
    exact hAz.trans (hvz.trans (hoz.trans hiz.symm))

  have hAll := Measure.eqOn_open_of_ae_eq hAB isOpen_Ioo hAc hBc
  intro t ht
  have he := hAll ht
  have hLpAE := Lp.ext_iff.mp he
  filter_upwards [hA t ht,hLpAE,scalarEnergy_chartRestrictionCLM_coe g μ hμ x hV hVc
    (hVO.trans (subset_closure.trans hOt)) (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))] with z hAz hEq hR
  exact hAz.symm.trans (hEq.trans hR)

/-- The actual supported variational heat path supplies all hypotheses
of the proved native homogeneous interior smoothing theorem. -/
theorem dirichletHeat_chartInteriorRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOt : closure O ⊆ chartTarget x)
    (hOΩ : chartInv x '' O ⊆ Ω) {l r : ℝ} (hl : 0 < l) (hlr : l < r)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃ v : Parabolic.Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo l r), (fun z => v (z,t)) =ᵐ[volume.restrict O]
        scalarEnergy_chartRestrictionCLM g μ hμ x hO hOc hOt
          (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f))) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  obtain ⟨u,G,hE,hEq,hSlices⟩ :=
    dirichletHeat_chartWeakSolution g hK μ hμ Ω hΩ x hO hOc hOt hOΩ hl hlr f
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g x hOc hOt (Set.Ioo l r)
  have hEllO : Parabolic.Elliptic (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p ⟨subset_closure hp.1,hp.2⟩⟩
  obtain ⟨v,hv,hAE,hClass⟩ := L16Interior.homogeneousInteriorSmoothing n hn O l r lam upper hO hlr
    (scalarHeatChartCoeff g x) (fun _ _ => 0) u G
    (scalarHeatChartCoeff_smooth g x (subset_closure.trans hOt) (Set.Ioo l r)) hEllO hE hEq
  refine ⟨v,hv,?_,hClass⟩
  have hAEslice := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hAE)
  filter_upwards [hAEslice,hSlices] with t ht hS
  filter_upwards [ht,hS] with z hz hR
  exact hz.symm.trans hR

/-- Actual local classical heat on every positive time slice, with no
regularity or boundary-value inlet. -/
theorem dirichletHeat_chartClassicalRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (x : M.Carrier) {O V : Set (ComplexVector n)} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (hOt : closure O ⊆ chartTarget x)
    (hOΩ : chartInv x '' O ⊆ Ω) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) {l r : ℝ} (hl : 0 < l) (hlr : l < r)
    (f : Lp ℝ 2 (μ.restrict Ω)) :
    ∃ v : Parabolic.Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      (∀ t ∈ Set.Ioo l r, (fun z => v (z,t)) =ᵐ[volume.restrict V]
        (fun z => (l2ZeroExtension μ Ω hΩ (dirichletHeat g μ hμ Ω t f)) (chartInv x z))) ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r,
        Parabolic.linearOp (O ×ˢ Set.Ioo l r) (scalarHeatChartCoeff g x) (fun _ _ => 0) v p = 0 := by
  obtain ⟨v,hv,hAE,hClass⟩ :=
    dirichletHeat_chartInteriorRepresentative hn g hK μ hμ Ω hΩ x hO hOc hOt hOΩ hl hlr f
  exact ⟨v,hv,dirichletHeat_chart_smoothSlice_every_time g μ hμ Ω hΩ x hO hOc hOt
    hV hVc hVO hl f hv hAE,hClass⟩

end Yau.Proofs.F03Aux
