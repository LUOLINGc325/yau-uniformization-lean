import Yau.Proofs.C01Final
import Yau.Proofs.EnvelopeRootApplication

noncomputable section
namespace Yau.NodeProofs

theorem C01_proved : Yau.Blueprint.C01 := C01Aux.C01_of_E03 E03_actual_proved

theorem C01_contract_proved : Yau.BlueprintContracts.C01_contract := C01_proved

end Yau.NodeProofs
