import Yau.Proofs.F03
import Yau.Proofs.P06
import Yau.Proofs.P07
import Yau.Proofs.P08
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs

theorem F03_proved : Yau.Blueprint.F03 :=
  Yau.Proofs.F03_of_P06_P07_P08 P06_proved P07_proved P08_proved

theorem F03_contract_proved : Yau.BlueprintContracts.F03_contract := F03_proved

end Yau.NodeProofs
