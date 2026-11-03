import Yau.Geometry.Basic

/-! Native connectedness glues actual local forward positivity at arbitrary times. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux

def ForwardPositive {X : Type*} (u : X → ℝ → ℝ) (x y : X) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t → 0 < u x s → 0 < u y t

theorem forwardPositive_trans {X : Type*} (u : X → ℝ → ℝ) {x y z : X}
    (hxy : ForwardPositive u x y) (hyz : ForwardPositive u y z) : ForwardPositive u x z := by
  intro s t hs hst hux
  have hsm : s < (s+t)/2 := by linarith only [hst]
  have hmt : (s+t)/2 < t := by linarith only [hst]
  exact hyz ((s+t)/2) t (hs.trans hsm) hmt (hxy s ((s+t)/2) hs hsm hux)

/-- The local input here is precisely the two directions of the ordinary
chart-bump comparison. Connectedness adds no Harnack or kernel premise. -/
theorem forwardPositive_on_preconnected {X : Type*} [TopologicalSpace X]
    (u : X → ℝ → ℝ) {O : Set X} (hO : IsPreconnected O)
    (hlocal : ∀ x ∈ O, ∀ᶠ y in 𝓝[O] x,
      ForwardPositive u x y ∧ ForwardPositive u y x)
    {x y : X} (hx : x ∈ O) (hy : y ∈ O) : ForwardPositive u x y := by
  exact hO.induction₂' (ForwardPositive u) hlocal
    (fun _ _ _ _ _ _ => forwardPositive_trans u) hx hy

end Yau.Proofs.F03Aux
