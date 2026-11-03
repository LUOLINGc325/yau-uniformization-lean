import Yau.Proofs.Y01Original
import Yau.Proofs.Y02
import Yau.Proofs.Y03
import Yau.Proofs.Y05
import Yau.Proofs.Y06RootApplication
import Yau.Proofs.Y07
import Yau.Proofs.Y04

noncomputable section
namespace Yau.NodeProofs

theorem Y01_proved : Yau.Blueprint.Y01 :=
  Yau.Proofs.Y01Aux.Y01_of_original_predecessors
    Yau.Proofs.Y02 Yau.Blueprint.Alignment.Y03Proof.y03
    Yau.Proofs.Y05Aux.Y05_proved Y06_proved Y07_proved

theorem Y01_contract_proved : Yau.BlueprintContracts.Y01_contract := Y01_proved

theorem Y04_proved : Yau.Blueprint.Y04 :=
  Yau.Proofs.Y04_of_originalY01 Y01_proved

theorem Y04_contract_proved : Yau.BlueprintContracts.Y04_contract := Y04_proved

end Yau.NodeProofs
