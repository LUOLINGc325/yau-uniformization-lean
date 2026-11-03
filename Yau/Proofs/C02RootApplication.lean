import Yau.Proofs.C02
import Yau.Proofs.C01RootApplication
import Yau.LeafProofs.L23

noncomputable section
namespace Yau.NodeProofs

theorem C02_proved : Yau.Blueprint.C02 :=
  Yau.Proofs.C02 C01_proved Yau.LeafProofs.L23

theorem C02_contract_proved : Yau.BlueprintContracts.C02_contract := C02_proved

end Yau.NodeProofs
