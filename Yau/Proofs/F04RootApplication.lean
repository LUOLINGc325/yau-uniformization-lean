import Yau.Proofs.F04Complete
import Yau.Proofs.P07
import Yau.Proofs.F03RootApplication
import Yau.Proofs.G02
import Yau.Proofs.F05

noncomputable section
namespace Yau.NodeProofs

theorem F04_proved : Yau.Blueprint.F04 :=
  Yau.F04Proof.F04_of_registered_dependencies
    P07_proved F03_proved G02_proved Yau.Proofs.F05

theorem F04_contract_proved : Yau.BlueprintContracts.F04_contract := F04_proved

end Yau.NodeProofs
