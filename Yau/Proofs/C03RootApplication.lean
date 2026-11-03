import Yau.Proofs.C03Paper

noncomputable section
namespace Yau.NodeProofs

theorem C03_proved : Yau.Blueprint.C03 := Yau.Proofs.C03Aux.C03_contract_unconditional

theorem C03_contract_proved : Yau.BlueprintContracts.C03_contract := C03_proved

end Yau.NodeProofs
