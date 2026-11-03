import Yau.Proofs.F03DirichletCoreGenerator
import Yau.LeafProofs.L19HeatUniformBounds
import Yau.Proofs.F03DirichletHeatMarkov

/-! Genuine supported compact Duhamel and uniform initial estimates. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletHeat_continuousOn_nonneg (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f : Lp ℝ 2 (μ.restrict O)) :
    ContinuousOn (fun t => dirichletHeat g μ hμ O t f) (Set.Ici (0 : ℝ)) := by
  intro t ht
  have ht0 : 0 ≤ t := ht
  rcases ht0.eq_or_lt with rfl | ht
  · simpa only [ContinuousWithinAt,dirichletHeat_zero,one_apply_eq_self] using
      dirichletHeat_tendsto_zero g μ hμ O hO f
  · exact (dirichletHeat_apply_hasDerivAt g μ hμ O ht f).continuousAt.continuousWithinAt

theorem dirichletHeat_compact_duhamel (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (k : dirichletCore g μ hμ O)
    {T : ℝ} (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, dirichletHeat g μ hμ O s
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))) =
      dirichletHeat g μ hμ O T (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) -
        l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) := by
  have hcont := (dirichletHeat_continuousOn_nonneg g μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val))).mono
      (show Set.Icc (0 : ℝ) T ⊆ Set.Ici 0 from Set.Icc_subset_Ici_self)
  have hcontL := (dirichletHeat_continuousOn_nonneg g μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))).mono
      (show Set.Icc (0 : ℝ) T ⊆ Set.Ici 0 from Set.Icc_subset_Ici_self)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hcont
    (fun s hs => dirichletHeat_compact_hasDerivAt g hK μ hμ O hO.measurableSet k hs.1)
    (ContinuousOn.intervalIntegrable_of_Icc hT.le hcontL)
  simpa only [dirichletHeat_zero,one_apply_eq_self] using hFTC

theorem dirichletHeat_compact_initial_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (k : dirichletCore g μ hμ O)
    {K T : ℝ} (hK0 : 0 < K) (hT : 0 < T)
    (hLap : ∀ x, |laplacian g.form k.val x| ≤ K) :
    ∀ᵐ x ∂μ.restrict O,
      |dirichletHeat g μ hμ O T (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) x-k.val x| ≤ T*K := by
  have hL : ∀ᵐ x ∂μ.restrict O,
      |l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)) x| ≤ K := by
    filter_upwards [restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)),
      ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ (scalarCompactLaplacian g μ hμ k.val))]
      with x hr hx
    change |restrictL2 μ O _ x| ≤ K
    rw [hr,hx]
    exact hLap x
  have hcont := dirichletHeat_continuousOn_nonneg g μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))
  have hInt : IntervalIntegrable (fun s => dirichletHeat g μ hμ O s
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ (scalarCompactLaplacian g μ hμ k.val)))) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (hcont.mono Set.Icc_subset_Ici_self)
  have hbound := lp_interval_integral_uniform_bound (μ.restrict O) hT hK0.le hInt
    (fun t ht => dirichletHeat_abs_markov g μ hμ O hO.measurableSet ht.1.le K hK0 _ hL)
  rw [dirichletHeat_compact_duhamel g hK μ hμ O hO k hT] at hbound
  filter_upwards [hbound,Lp.coeFn_sub
    (dirichletHeat g μ hμ O T (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)))
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)),
    restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ k.val),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ k.val)] with x hx hs hr hk
  have hkr : l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val) x=k.val x :=
    hr.trans hk
  simpa only [hs,Pi.sub_apply,hkr] using hx

end Yau.Proofs.F03Aux
