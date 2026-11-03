import spec.CHAIN.CONTRACTS
import Yau.LeafProofs.L14Exact
import Yau.LeafProofs.L25
import Yau.Proofs.B01
import Yau.Proofs.D03Closure

noncomputable section

namespace Yau.NodeProofs
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

/-- The full intrinsic extra-integrability theorem from its exact original
predecessors. All bundle, metric and map data remain those of the frozen target. -/
theorem D03_of_predecessors
    (hL14 : Yau.LeafObligations.L14)
    (hL25 : Yau.LeafObligations.L25)
    (hB01 : Yau.Blueprint.B01) : Yau.Blueprint.D03 := by
  intro M c hc r q E _ _ _ _ _ _ _ k A hE hk hG hHA hA hBound s hs hInt
  rcases hB01 with ⟨_, hComplete, _, _, _⟩
  obtain ⟨g, μ, hμ, _⟩ := hComplete M c hc
  have hSolve := (hL14 1 r M E).1
  obtain ⟨b, hb, hbFinite, hbExtra, hbConv⟩ :=
    Yau.Proofs.D03Aux.exists_extra_approximants E hSolve c hc g μ hμ k hE hk hG s hs hInt
  exact Yau.Proofs.D03Aux.extra_integrability_of_approximants E hL25 c hc k hk A hE hHA hA hBound
    s hs hInt b hb hbFinite hbExtra hbConv

/-- Unconditional exact D03, with the accepted predecessor proofs discharged. -/
theorem D03_proved : Yau.Blueprint.D03 :=
  D03_of_predecessors Yau.LeafProofs.L14 Yau.LeafProofs.L25 Yau.NodeProofs.B01_proved

theorem D03_contract_proved : Yau.BlueprintContracts.D03_contract := D03_proved

end Yau.NodeProofs
