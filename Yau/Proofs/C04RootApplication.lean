import Yau.Proofs.C04Original
import Yau.Proofs.C01RootApplication
import Yau.Proofs.C02RootApplication
import Yau.Proofs.C03RootApplication

noncomputable section
namespace Yau.NodeProofs

theorem C04_proved : Yau.Blueprint.C04 :=
  Yau.Proofs.C04Aux.C04_of_originalC01_C02_C03 Yau.NodeProofs.C01_proved Yau.NodeProofs.C02_proved Yau.NodeProofs.C03_proved

theorem C04_contract_proved : Yau.BlueprintContracts.C04_contract :=
  C04_proved

end Yau.NodeProofs
