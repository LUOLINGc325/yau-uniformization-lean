import Mathlib.Topology.Instances.EReal.Lemmas

/-! SOURCE-ONLY E03 candidate. The actual chart transitions must construct every input below. -/

noncomputable section
open scoped Topology
open Filter Set

namespace Yau.NodeProofs.E03Aux

theorem liminf_eq_of_two_continuous_germ_transports
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (f : P → EReal) (g : Q → EReal) (p : P) (q : Q)
    (e : P → Q) (i : Q → P)
    (he : Tendsto e (𝓝 p) (𝓝 q)) (hi : Tendsto i (𝓝 q) (𝓝 p))
    (hf : (fun x => g (e x)) =ᶠ[𝓝 p] f)
    (hg : (fun y => f (i y)) =ᶠ[𝓝 q] g) :
    liminf f (𝓝 p) = liminf g (𝓝 q) := by
  change sSup {a : EReal | ∀ᶠ x in 𝓝 p, a ≤ f x} =
    sSup {a : EReal | ∀ᶠ y in 𝓝 q, a ≤ g y}
  congr 1
  ext a
  constructor
  · intro ha
    filter_upwards [hi.eventually ha, hg] with y hy hgy
    simpa only [hgy] using hy
  · intro ha
    filter_upwards [he.eventually ha, hf] with x hx hfx
    simpa only [hfx] using hx

end Yau.NodeProofs.E03Aux
