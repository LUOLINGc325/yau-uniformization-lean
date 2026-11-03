import Yau.Proofs.V01ContactWitness
import Yau.Proofs.V01Zero

/-! The original envelope inequality, with only its exact named producers.
Original V02 and V04 must be bound before an unconditional root is asserted. -/

noncomputable section
namespace Yau.Proofs
open Yau.Blueprint Yau.BlueprintContracts Yau.Blueprint.V01Proof

theorem V01_of_parents
    (hP03 : P03_contract) (hP07 : P07_contract) (hF04 : F04_contract)
    (hD05 : D05_contract) (hV02 : V02_contract) (hV03 : V03_contract)
    (hV04 : V04_contract) (hV05 : V05_contract) : V01_contract := by
  intro n X o h U P ρ hloc
  by_cases hn : n = 0
  · subst n
    exact envelopeInequality_zero X h
  · obtain ⟨u, hu⟩ := hP07 n X o
    intro T hT x z η s hz hs hST φ hφ hφeq hφle W hC
    exact original_contact_schur_witness o h U P ρ hloc (hF04 n X o h U P ρ hloc)
      (hP03 n X) u hu (hV05 n) (hD05 n X) (hV02 n X) (hV03 n X) (hV04 n X)
      T hT x z hz η s ⟨hs, hST⟩ φ hφ hφeq hφle hC

end Yau.Proofs
