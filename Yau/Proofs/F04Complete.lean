import Yau.Proofs.F04Minimality
import Yau.Proofs.F04SupercaloricTails
import Yau.Proofs.F04NonlinearComparison

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- Conditional assembly of the ORIGINAL unchanged F04 target from only
 EXACT registered dependency contracts. All internal volume, energy,
 source, regularity, exhaustion-limit, tail and comparison constructions
 are genuine proofs in the imported owned sources. This theorem does NOT
 discharge the registered predecessors or claim the node unconditional. -/
theorem F04_of_registered_dependencies
    (hP07 : P07) (hF03 : F03) (hG02 : G02) (hF05 : F05) : F04 := by
  intro n X o h U P ρ hloc
  by_cases hn : n = 0
  · subst n
    exact scalarComparison_dimension_zero X o h U P ρ hloc
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  intro T hT
  refine ⟨?_,?_,?_,?_⟩
  · intro x t ht
    simpa only [source] using rho_source_equation o h U P ρ hloc T hT x t ht
  · intro ρ' hρ' hρ'Pos hρ'0 hρ'Eq
    exact rho_minimal_from_dependencies hP07 hF03 hG02 X o h U P ρ hloc hT ρ' hρ' hρ'Pos hρ'0 hρ'Eq
  · exact flow_supercaloric_tails_from_dependencies hP07 hF03 hG02 hnPos X o h U P ρ hloc hT
  · exact flow_nonlinear_comparison_from_dependencies hP07 hF03 hG02 hF05 X o h U P ρ hloc hT

end Yau.F04Proof
