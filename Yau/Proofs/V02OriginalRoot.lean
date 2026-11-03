import Yau.Proofs.D02
import Yau.Proofs.V02
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs

theorem V02_proved : Yau.Blueprint.V02 := by
  intro n X
  exact Yau.Blueprint.V02Proof.V02_of_originalD02 (D02_proved n X)

theorem V02_contract_proved : Yau.BlueprintContracts.V02_contract := V02_proved

end Yau.NodeProofs
