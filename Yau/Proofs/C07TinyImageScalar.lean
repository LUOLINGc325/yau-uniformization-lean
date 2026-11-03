import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

open scoped Topology unitInterval

noncomputable section

namespace Yau.Proofs.C07TinyImageAux

open Set Filter

/-- A continuous function starting below a positive level cannot reach it
if the same strict bound holds at every initial segment staying below it. -/
theorem below_of_prefix_bound {D : I → ℝ} (hD : Continuous D) (hD0 : D 0 = 0)
    {q : ℝ} (hq : 0 < q)
    (hbound : ∀ τ : I, (∀ a : I, a ≤ τ → D a ≤ q) → D τ < q) :
    ∀ a : I, D a < q := by
  have hit : ∀ a : I, q ≤ D a → ∃ b : I, b ≤ a ∧ D b = q := by
    intro a ha
    have h0a : (0 : I) ≤ a := a.2.1
    obtain ⟨b, hb, hDb⟩ := intermediate_value_Icc h0a hD.continuousOn
      (show q ∈ Icc (D 0) (D a) from ⟨by rw [hD0]; exact hq.le, ha⟩)
    exact ⟨b, hb.2, hDb⟩
  intro a
  by_contra ha
  obtain ⟨b, _, hb⟩ := hit a (le_of_not_gt ha)
  have hlevel : IsCompact {b : I | D b = q} := (isClosed_eq hD continuous_const).isCompact
  obtain ⟨τ, hτ⟩ := hlevel.exists_isLeast ⟨b, hb⟩
  have hprefix : ∀ b : I, b ≤ τ → D b ≤ q := by
    intro b hbτ
    by_contra hbq
    have hqb : q < D b := lt_of_not_ge hbq
    obtain ⟨c, hcb, hDc⟩ := hit b hqb.le
    have hτc : τ ≤ c := hτ.2 hDc
    have hbc : b = c := le_antisymm (hbτ.trans hτc) hcb
    rw [← hbc] at hDc
    exact (ne_of_lt hqb) hDc.symm
  have hτeq : D τ = q := hτ.1
  exact (not_lt_of_ge hτeq.ge) (hbound τ hprefix)

end Yau.Proofs.C07TinyImageAux
