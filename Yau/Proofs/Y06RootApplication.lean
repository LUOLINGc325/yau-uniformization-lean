import Yau.Proofs.Y06Original
import Yau.Proofs.Y02

noncomputable section
namespace Yau.NodeProofs

theorem Y06_proved : Yau.Blueprint.Y06 :=
  Yau.Proofs.Y06Aux.Y06_of_original_predecessors Yau.Proofs.Y02

theorem Y06_contract_proved : Yau.BlueprintContracts.Y06_contract := Y06_proved

end Yau.NodeProofs
