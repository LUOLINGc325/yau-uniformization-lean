import Yau.Proofs.F03BoundaryComparison
import Yau.Proofs.F03BoundaryBarrierTest
import Yau.Proofs.F03BoundarySourceBound

/-! Genuine zero lateral limit of positive supported heat, with no trace premise. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem dirichletClassicalHeat_boundary_zero (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
    {t : ℝ} (ht : 0 < t) (p : M.Carrier) (hp : p ∈ frontier Ω) :
    Tendsto (fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t) (𝓝[Ω] p) (𝓝 0) := by
  obtain ⟨C,hC,hU⟩ := dirichletClassicalHeat_compact_boundary_bound g hK μ hμ Ω hΩ.1
    (closure Ω) hΩ.2.2.2.1 ht
  obtain ⟨B,hB,hF⟩ := dirichletHeatInverse_boundary_abs_bound g hK μ hμ Ω hΩ ht
  have hs : 0 ≤ C*‖f‖ := mul_nonneg hC.le (norm_nonneg _)
  have hR : 0 ≤ B*‖f‖ := mul_nonneg hB.le (norm_nonneg _)
  obtain ⟨a,δ,c,k,hδ,hc,hpsrc,hδt,hk,hkc,hkp,hk0,hks,hkL⟩ :=
    exists_actual_coercive_boundary_test g Ω hΩ p hp (C*‖f‖) (B*‖f‖) hs hR
  let K : ScalarEnergyDomain g μ hμ := ⟨k,hk,hkc⟩
  have hsource : ∀ᵐ x ∂μ.restrict Ω,
      K x+c < dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t →
        dirichletHeatInverse g μ hμ Ω t f x ≤ K x+c-laplacian g.form (fun y => K y+c) x := by
    filter_upwards [hF f t le_rfl,ae_restrict_mem hΩ.1.measurableSet] with x hxF hxΩ
    intro hactive
    have hxinner : x ∈ chartInv a '' Metric.ball (chartPt a p) (δ/4) := by
      by_contra hout
      have hlarge := hks x hxΩ hout
      have hsmall := (le_abs_self _).trans (hU f t le_rfl x (subset_closure hxΩ) hxΩ)
      exact (not_lt_of_ge (hsmall.trans hlarge)) hactive
    exact (le_abs_self _).trans (hxF.trans (hkL x hxΩ hxinner))
  have hUpper := dirichletHeat_le_affine_barrier g hK μ hμ Ω hΩ f ht K c hk0 hsource
  have hSmooth : SmoothFn (fun x => k x+c) := fun a => (hk a).add contDiffOn_const
  have hLimit : Tendsto (fun x => k x+c) (𝓝[Ω] p) (𝓝 0) := by
    simpa only [hkp] using ((continuous_of_smoothFn hSmooth).tendsto p).mono_left nhdsWithin_le_nhds
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with x hxΩ
    exact hb.trans_le (dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ.1 f hf ht x hxΩ)
  · intro b hb
    filter_upwards [hLimit.eventually (eventually_lt_nhds hb),self_mem_nhdsWithin] with x hx hxΩ
    exact (hUpper x hxΩ).trans_lt hx

end Yau.Proofs.F03Aux
