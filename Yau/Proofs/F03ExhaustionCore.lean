import Yau.Proofs.F03DirichletEnergy
import spec.CHAIN.HeatConcreteBindings

/-! The original exhaustion eventually contains every genuine energy core. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem smoothExhaustion_monotone {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) :
    Monotone O := monotone_nat_of_le_succ (fun j => subset_closure.trans (hO.2.1 j))

theorem smoothExhaustion_eventually_contains_compact {O : ℕ → Set M.Carrier}
    (hO : SmoothExhaustion O) {K : Set M.Carrier} (hK : IsCompact K) :
    ∀ᶠ j in atTop, K ⊆ O j := by
  have hmono := smoothExhaustion_monotone hO
  have hcover : K ⊆ ⋃ j, O j := by rw [hO.2.2];exact subset_univ K
  obtain ⟨J,hJ⟩ := hK.elim_directed_cover O (fun j => (hO.1 j).1) hcover
    (fun i j => ⟨max i j,hmono (le_max_left _ _),hmono (le_max_right _ _)⟩)
  exact eventually_atTop.2 ⟨J,fun j hj => hJ.trans (hmono hj)⟩

theorem smoothExhaustion_eventually_core (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O) (f : ScalarEnergyDomain g μ hμ) :
    ∀ᶠ j in atTop, f ∈ dirichletCore g μ hμ (O j) :=
  smoothExhaustion_eventually_contains_compact hO f.2.2

theorem smoothExhaustion_energy_approx (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {O : ℕ → Set M.Carrier} (hO : SmoothExhaustion O)
    (u : ScalarEnergySpace g μ hμ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∃ v : DirichletEnergy g μ hμ (O j), ‖v.val-u‖ < ε := by
  obtain ⟨f,hf⟩ := (UniformSpace.Completion.denseRange_coe
    (α := ScalarEnergyDomain g μ hμ)).exists_dist_lt u hε
  filter_upwards [smoothExhaustion_eventually_core g μ hμ hO f] with j hj
  refine ⟨dirichletCoreToEnergy g μ hμ (O j) ⟨f,hj⟩,?_⟩
  change ‖(f : ScalarEnergySpace g μ hμ)-u‖ < ε
  rw [norm_sub_rev]
  simpa only [dist_eq_norm] using hf

end Yau.Proofs.F03Aux
