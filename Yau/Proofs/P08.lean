import Yau.Proofs.P08Assembly
import Yau.Proofs.P04
import Yau.Proofs.P07
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs

theorem P08_proved : Yau.Blueprint.P08 :=
  P08Aux.P08_of_P04_P07 P04_proved P07_proved

theorem P08_contract_proved : Yau.BlueprintContracts.P08_contract := P08_proved

end Yau.NodeProofs
