import Mathlib

/-! The pure real-order continuation step. A positive admissible time set
that contains its positive cofinal endpoints and extends at every point
below the fixed horizon contains the horizon itself. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux

theorem F05_finite_horizon_principle {E : Set ℝ} {S : ℝ}
    (hPositive : ∃ t ∈ E, 0 < t) (hUpper : ∀ t ∈ E, t ≤ S)
    (hClosed : ∀ τ : ℝ, 0 < τ → τ ≤ S →
      (∀ ε : ℝ, 0 < ε → ∃ t ∈ E, τ-ε < t ∧ t ≤ τ) → τ ∈ E)
    (hExtend : ∀ τ ∈ E, τ < S → ∃ t ∈ E, τ < t) : S ∈ E := by
  obtain ⟨t0,ht0,ht0pos⟩ := hPositive
  have hE : E.Nonempty := ⟨t0,ht0⟩
  have hBound : BddAbove E := ⟨S,fun t ht => hUpper t ht⟩
  let τ := sSup E
  have hτpos : 0 < τ := ht0pos.trans_le (le_csSup hBound ht0)
  have hτS : τ ≤ S := csSup_le hE hUpper
  have hτMem : τ ∈ E := hClosed τ hτpos hτS (by
    intro ε hε
    obtain ⟨t,ht,hNear⟩ := exists_lt_of_lt_csSup hE (show τ-ε < sSup E by dsimp only [τ]; linarith)
    exact ⟨t,ht,hNear,le_csSup hBound ht⟩)
  have hEq : τ = S := by
    apply le_antisymm hτS
    apply not_lt.mp
    intro hLt
    obtain ⟨t,ht,hτt⟩ := hExtend τ hτMem hLt
    exact (not_lt_of_ge (le_csSup hBound ht)) hτt
  rwa [← hEq]

end Yau.Proofs.F05Aux
