import Yau.Proofs.Y07GridTail
import spec.CHAIN.CONTRACTS

namespace Yau.NodeProofs

/-- The unchanged canonical-grid tail contract, with its exact index offset. -/
theorem Y07_proved : Yau.Blueprint.Y07 := Y07Aux.canonicalGridTail

theorem Y07_contract_proved : Yau.BlueprintContracts.Y07_contract := Y07_proved

end Yau.NodeProofs
