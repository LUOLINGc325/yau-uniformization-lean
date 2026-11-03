import Yau.Proofs.F04MassCutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

/-- Open supported-energy domains from the original controlled exhaustion.
No regular-value or smooth-boundary assertion is needed. -/
def potentialDomain {α : Type*} (u : α → ℝ) (j : ℕ) : Set α :=
  {x | u x < (j : ℝ) + 2}

theorem potentialDomain_open {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (j : ℕ) :
    IsOpen (potentialDomain u j) :=
  isOpen_lt (LeafProofs.L18Aux.continuous_of_smoothFn hu.1) continuous_const

theorem potentialDomain_closure_sublevel {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (j : ℕ) :
    closure (potentialDomain u j) ⊆ {x | u x ≤ (j : ℝ) + 2} := by
  apply closure_minimal ?_ (isClosed_le (LeafProofs.L18Aux.continuous_of_smoothFn hu.1) continuous_const)
  intro x hx
  change u x < (j : ℝ) + 2 at hx
  exact le_of_lt hx

theorem potentialDomain_compact_closure {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (j : ℕ) :
    IsCompact (closure (potentialDomain u j)) :=
  (hu.2.1 ((j : ℝ) + 2)).of_isClosed_subset isClosed_closure
    (potentialDomain_closure_sublevel X o u hu j)

theorem potentialDomain_mono {α : Type*} (u : α → ℝ) : Monotone (potentialDomain u) := by
  intro i j hij x hx
  change u x < (j : ℝ) + 2
  change u x < (i : ℝ) + 2 at hx
  have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  linarith

theorem potentialDomain_closure_succ {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (j : ℕ) :
    closure (potentialDomain u j) ⊆ potentialDomain u (j + 1) := by
  intro x hx
  have hh := potentialDomain_closure_sublevel X o u hu j hx
  change u x ≤ (j : ℝ) + 2 at hh
  change u x < ((j + 1 : ℕ) : ℝ) + 2
  rw [Nat.cast_add, Nat.cast_one]
  linarith

theorem potentialDomain_eventually_contains_compact {n : ℕ} (X : KahlerManifold n)
    (o : Pt X) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ N : ℕ, ∀ j ≥ N, K ⊆ potentialDomain u j := by
  obtain ⟨B, hB⟩ := (hK.image (LeafProofs.L18Aux.continuous_of_smoothFn hu.1)).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt B
  refine ⟨N, ?_⟩
  intro j hj x hx
  have hBx : u x ≤ B := hB (mem_image_of_mem u hx)
  have hNj : (N : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
  change u x < (j : ℝ) + 2
  linarith

end Yau.F04Proof
