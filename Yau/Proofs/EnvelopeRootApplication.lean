import Yau.Proofs.V01
import Yau.Proofs.E02Complete
import Yau.Proofs.E03
import Yau.Proofs.E01
import Yau.Proofs.F04RootApplication
import Yau.Proofs.P03
import Yau.Proofs.P07
import Yau.Proofs.D05
import Yau.Proofs.V02OriginalRoot
import Yau.Proofs.V03
import Yau.Proofs.V04Original
import Yau.Proofs.V05

noncomputable section
namespace Yau.NodeProofs

theorem V01_proved : Yau.Blueprint.V01 :=
  Yau.Proofs.V01_of_parents P03_proved P07_proved F04_proved
    D05_proved V02_proved Yau.Blueprint.V03Proof.v03
    Yau.Blueprint.V04Proof.v04 V05_proved

theorem V01_contract_proved : Yau.BlueprintContracts.V01_contract := V01_proved

theorem E02_proved : Yau.Blueprint.E02 := E02_of_E01_V01 E01_proved V01_proved

theorem E02_contract_proved : Yau.BlueprintContracts.E02_contract := E02_proved

theorem E03_actual_proved : Yau.Blueprint.E03 := E03_proved E01_proved E02_proved F04_proved

theorem E03_contract_proved : Yau.BlueprintContracts.E03_contract := E03_actual_proved

end Yau.NodeProofs
