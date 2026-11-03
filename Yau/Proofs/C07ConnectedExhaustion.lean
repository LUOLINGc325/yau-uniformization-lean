import Yau.Proofs.C07ConnectedExhaustionNeighborhood

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07ConnectedExhaustionAux

open Yau Set

variable {n : ℕ} {M : ComplexManifold n}

/-- A connected manifold admits a nested exhaustion by connected open sets
with compact closures, all containing a prescribed base point. -/
theorem exists_connected_exhaustion (o : M.Carrier) :
    ∃ V : ℕ → Set M.Carrier,
      (∀ j, IsOpen (V j) ∧ IsPreconnected (V j) ∧ IsCompact (closure (V j)) ∧ o ∈ V j) ∧
      (∀ j, closure (V j) ⊆ V (j + 1)) ∧
      ∀ K : Set M.Carrier, IsCompact K → ∃ j, K ⊆ V j := by
  classical
  letI : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  let E := CompactExhaustion.choice M.Carrier
  let T := {V : Set M.Carrier //
    IsOpen V ∧ IsPreconnected V ∧ IsCompact (closure V) ∧ o ∈ V}
  choose U hUo hUp hUc hoU hKU using
    fun K : {K : Set M.Carrier // IsCompact K} => exists_precompact_preconnected_open o K.2
  let grow : {K : Set M.Carrier // IsCompact K} → T :=
    fun K => ⟨U K, hUo K, hUp K, hUc K, hoU K⟩
  have hgrow : ∀ K : {K : Set M.Carrier // IsCompact K}, K.1 ⊆ (grow K).1 := hKU
  let W : ℕ → T := Nat.rec (grow ⟨E 0, E.isCompact 0⟩) fun j V =>
    grow ⟨closure V.1 ∪ E (j + 1), V.2.2.2.1.union (E.isCompact (j + 1))⟩
  have hstep : ∀ j, closure (W j).1 ⊆ (W (j + 1)).1 := by
    intro j
    exact subset_union_left.trans (hgrow
      ⟨closure (W j).1 ∪ E (j + 1), (W j).2.2.2.1.union (E.isCompact (j + 1))⟩)
  have hEW : ∀ j, E j ⊆ (W j).1 := by
    intro j
    cases j with
    | zero => exact hgrow ⟨E 0, E.isCompact 0⟩
    | succ j => exact subset_union_right.trans (hgrow
        ⟨closure (W j).1 ∪ E (j + 1), (W j).2.2.2.1.union (E.isCompact (j + 1))⟩)
  refine ⟨fun j => (W j).1, fun j => (W j).2, hstep, ?_⟩
  intro K hK
  obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact hK
  exact ⟨j, hj.trans (hEW j)⟩

end Yau.Proofs.C07ConnectedExhaustionAux
