import Yau.Proofs.F01SpatialWordLeibniz

/-! The differentiated linear forcing contains exactly the terms with
at least one derivative on the coefficient. Thus its solution Hessians
use strictly fewer derivative words than the principal term. -/
namespace Yau.NodeProofs.F01Aux
variable {E : Type*}

def linearSpatialCommutatorPairs : List E → List (List E × List E)
  | [] => []
  | v :: vs => ([v], vs) ::
      ((linearSpatialCommutatorPairs vs).map (fun ab => (v :: ab.1, ab.2)) ++
        (linearSpatialCommutatorPairs vs).map (fun ab => (ab.1, v :: ab.2)))

theorem linearSpatialCommutatorPairs_orders (vs : List E) :
    ∀ ab ∈ linearSpatialCommutatorPairs vs,
      ab.1 ≠ [] ∧ ab.1.length + ab.2.length = vs.length := by
  induction vs with
  | nil => simp [linearSpatialCommutatorPairs]
  | cons v vs ih =>
    intro ab hab
    rcases List.mem_cons.mp hab with h | h
    · subst ab
      simp only [ne_eq, List.cons_ne_self, List.cons_ne_nil, not_false_eq_true,
        List.length_cons, List.length_nil, zero_add, true_and]
      omega
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        obtain ⟨hne, hlen⟩ := ih p hp
        constructor
        · simp
        · simp only [List.length_cons]
          omega
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        obtain ⟨hne, hlen⟩ := ih p hp
        constructor
        · exact hne
        · simp only [List.length_cons]
          omega

theorem linearSpatialCommutatorPairs_lower_solution_order (vs : List E)
    {ab : List E × List E} (hab : ab ∈ linearSpatialCommutatorPairs vs) :
    ab.2.length < vs.length := by
  obtain ⟨hne, hlen⟩ := linearSpatialCommutatorPairs_orders vs ab hab
  have hp : 0 < ab.1.length := List.length_pos_of_ne_nil hne
  omega

theorem linearSpatialCommutatorPairs_count (vs : List E) :
    (linearSpatialCommutatorPairs vs).length + 1 = 2 ^ vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [linearSpatialCommutatorPairs, List.length_cons, List.length_append, List.length_map]
    rw [pow_succ]
    omega

end Yau.NodeProofs.F01Aux
