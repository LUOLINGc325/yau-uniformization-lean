import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! A compatible family of sections on closed intervals has a single section
on the interval below the supremum. One choice is made per time, for the
whole value in the arbitrary type `V`. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux

/-- Compatibility on overlaps makes all pointwise choices agree on every
closed prefix strictly below the supremum. -/
theorem compatible_sections_on_sup {V : Type*} (E : Set ℝ)
    (hE : E.Nonempty) (F : E → ℝ → V)
    (hcompat : ∀ a b : E, ∀ t, t ∈ Icc 0 (min (a : ℝ) b) → F a t = F b t) :
    ∃ f : ℝ → V, ∀ S : ℝ, S < sSup E →
      ∃ a : E, S < (a : ℝ) ∧ ∀ t, t ∈ Icc 0 S → f t = F a t := by
  classical
  let a0 : E := ⟨hE.choose, hE.choose_spec⟩
  have habove (t : ℝ) (ht : t < sSup E) : ∃ a : E, t < (a : ℝ) := by
    obtain ⟨a, ha, hta⟩ := exists_lt_of_lt_csSup hE ht
    exact ⟨⟨a, ha⟩, hta⟩
  let select : ℝ → E := fun t =>
    if ht : t < sSup E then (habove t ht).choose else a0
  have hselect (t : ℝ) (ht : t < sSup E) : t < (select t : ℝ) := by
    dsimp only [select]
    rw [dite_eq_left ht]
    exact (habove t ht).choose_spec
  refine ⟨fun t => F (select t) t, ?_⟩
  intro S hS
  obtain ⟨a, ha⟩ := habove S hS
  refine ⟨a, ha, ?_⟩
  intro t ht
  exact hcompat (select t) a t
    ⟨ht.1, le_min (hselect t (ht.2.trans_lt hS)).le (ht.2.trans ha.le)⟩

/-- A positive nonempty, horizon-bounded set of existence times has a positive
supremum bounded by that horizon. -/
theorem positive_sup_of_existence_times (E : Set ℝ) {H : ℝ}
    (hE : E.Nonempty) (hpos : ∀ T ∈ E, 0 < T) (hbound : ∀ T ∈ E, T ≤ H) :
    0 < sSup E ∧ sSup E ≤ H := by
  obtain ⟨T, hT⟩ := hE
  exact ⟨(hpos T hT).trans_le (le_csSup ⟨H, hbound⟩ hT), csSup_le ⟨T, hT⟩ hbound⟩

/-- A downward-closed property reaches the target closed horizon when its
supremal existence time admits a strictly longer solution. -/
theorem closed_horizon_of_sup_extension (P : ℝ → Prop) (H : ℝ)
    (hne : {T | 0 < T ∧ T ≤ H ∧ P T}.Nonempty)
    (hrestrict : ∀ T S, S ≤ T → P T → P S)
    (hext : ∃ Tnew, sSup {T | 0 < T ∧ T ≤ H ∧ P T} < Tnew ∧ P Tnew) :
    P H := by
  let E : Set ℝ := {T | 0 < T ∧ T ≤ H ∧ P T}
  have hsup := positive_sup_of_existence_times E hne
    (fun T hT => hT.1) (fun T hT => hT.2.1)
  obtain ⟨Tnew, hTnew, hnew⟩ := hext
  have hHsup : H ≤ sSup E := le_of_not_gt fun hsupH => by
    have hSsup : sSup E < min H Tnew := lt_min hsupH hTnew
    have hSE : min H Tnew ∈ E :=
      ⟨hsup.1.trans hSsup, min_le_left _ _,
        hrestrict Tnew (min H Tnew) (min_le_right _ _) hnew⟩
    have hle : min H Tnew ≤ sSup E := le_csSup ⟨H, fun T hT => hT.2.1⟩ hSE
    exact (not_lt_of_ge hle) hSsup
  exact hrestrict Tnew H (hHsup.trans hTnew.le) hnew

end Yau.NodeProofs.F01Aux
