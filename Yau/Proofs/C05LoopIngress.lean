import Yau.Proofs.C05LoopIngressDecay
import Yau.Proofs.C05LoopIngressLengthBound

/-! Original compact metric decay swallows every continuous loop in the actual good-time rescaled balls. -/
noncomputable section
open Filter
open scoped Topology Manifold unitInterval
namespace Yau.Proofs.C05LoopIngressAux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem loop_eventually_mem_rescaled_ball (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (tw : ℕ → ℝ)
    (htw : ∀ i, 0 < tw i) (htwinf : Tendsto tw atTop atTop)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (x : Pt X) (γ : Path x x) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ u : I,
      γ u ∈ distBall (scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))) o ε := by
  obtain ⟨B, a, L, _, ha, _, hbound⟩ :=
    eventually_uniform_loop_distance_bound X o h U P ρ hf hH tw htw htwinf hRi x γ
  have hsmall := eventually_small_sqrt_power_decay tw htwinf a B L ε ha hε
  filter_upwards [hbound, hsmall] with i hi hsmalli
  intro u
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  exact (hi u).trans_lt hsmalli

end Yau.Proofs.C05LoopIngressAux
