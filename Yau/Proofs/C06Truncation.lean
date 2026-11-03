import Yau.Proofs.D04Truncation

open scoped Topology
open Set Filter

noncomputable section

namespace Yau.Proofs.C06Aux

open Yau

variable {n : ℕ} {M : ComplexManifold n}

theorem isPsh_const (c : ℝ) : IsPsh (M := M) (fun _ => (c : EReal)) := by
  refine ⟨fun _ => EReal.coe_lt_top c, upperSemicontinuous_const, ?_⟩
  intro x z w _ φ hφ hmajor
  apply EReal.coe_le_coe_iff.mpr
  rw [← D04Aux.circleAverage_const c]
  exact D04Aux.circleAverage_mono continuous_const hφ
    (fun θ => EReal.coe_le_coe_iff.mp (hmajor θ))

theorem isPsh_max {u v : M.Carrier → EReal} (hu : IsPsh u) (hv : IsPsh v) :
    IsPsh (fun x => max (u x) (v x)) := by
  refine ⟨fun x => max_lt (hu.1 x) (hv.1 x), hu.2.1.sup hv.2.1, ?_⟩
  intro x z w hdisc φ hφ hmajor
  exact max_le
    (hu.2.2 x z w hdisc φ hφ (fun θ => (le_max_left _ _).trans (hmajor θ)))
    (hv.2.2 x z w hdisc φ hφ (fun θ => (le_max_right _ _).trans (hmajor θ)))

theorem isPsh_congr {u v : M.Carrier → EReal} (hu : IsPsh u) (heq : u = v) :
    IsPsh v := heq ▸ hu

/-- A finite lower truncation retains the original chart submean condition. -/
theorem isPsh_lowerTrunc {u : M.Carrier → EReal} (hu : IsPsh u) (j : ℕ) :
    IsPsh (fun x => (D04Aux.lowerTrunc u j x : EReal)) := by
  convert isPsh_max hu (isPsh_const (-(j : ℝ))) using 1
  funext x
  exact D04Aux.coe_lowerTrunc j (hu.1 x)

theorem upperSemicontinuous_of_coe {v : M.Carrier → ℝ}
    (hv : UpperSemicontinuous (fun x => (v x : EReal))) :
    UpperSemicontinuous v := by
  intro x a ha
  exact (hv x (a : EReal) (EReal.coe_lt_coe_iff.mpr ha)).mono
    (fun _ h => EReal.coe_lt_coe_iff.mp h)

/-- Equality of all finite truncations detects bottom values as well. -/
theorem eq_of_lowerTrunc_eq {u : M.Carrier → EReal}
    (hu : ∀ x, u x < ⊤) (h : ∀ j x y, D04Aux.lowerTrunc u j x = D04Aux.lowerTrunc u j y) :
    ∀ x y, u x = u y := by
  suffices hle : ∀ x y, u x ≤ u y by
    intro x y
    exact le_antisymm (hle x y) (hle y x)
  intro x y
  by_contra hxy
  have hyx : u y < u x := lt_of_not_ge hxy
  obtain ⟨a, hya, hax⟩ := EReal.exists_between_coe_real hyx
  obtain ⟨j, hj⟩ := exists_nat_gt (-a)
  have hja : -(j : ℝ) < a := by linarith
  have H := congrArg (fun r : ℝ => (r : EReal)) (h j x y)
  rw [D04Aux.coe_lowerTrunc j (hu x), D04Aux.coe_lowerTrunc j (hu y)] at H
  have hlo : ((-(j : ℝ) : ℝ) : EReal) < (a : EReal) := EReal.coe_lt_coe_iff.mpr hja
  have : max (u y) (((-(j : ℝ) : ℝ) : EReal)) < u x :=
    (max_lt hya hlo).trans hax
  exact (not_lt_of_ge (le_max_left _ _)) (H ▸ this)

end Yau.Proofs.C06Aux
