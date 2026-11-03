import spec.CHAIN.CONTRACTS
import Yau.Proofs.C05InputProducer
import Yau.Proofs.C05OriginalRigidity

/-! The exact original C05 derivation from its four registered predecessors. -/
noncomputable section
open scoped Topology
namespace Yau.Proofs.C05Aux
open Yau Blueprint BlueprintContracts

theorem C05_of_original_predecessors (hF01 : F01_contract) (hF04 : F04_contract)
    (hC01 : C01_contract) (hC04 : C04_contract) : C05_contract := by
  have hinputs := C05_input_producer_of_original_predecessors hF01 hF04 hC01 hC04
  intro n X
  let o : Pt X := Classical.choice inferInstance
  obtain ⟨h,U,P,ρ,hflow,hH,hW⟩ := hinputs n X o
  exact simplyConnected_of_original_flow o h U P ρ hflow hH hW

theorem C05_step_proved : C05_step_contract := by
  intro hF01 hF04 hC01 hC04
  exact ⟨C05_input_producer_of_original_predecessors hF01 hF04 hC01 hC04,
    C05_of_original_predecessors hF01 hF04 hC01 hC04⟩

end Yau.Proofs.C05Aux
