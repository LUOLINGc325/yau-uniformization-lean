import Yau.Proofs.U02Original
import Yau.Proofs.U01

/-! Original U02, using the accepted original backward-shadowing theorem. -/

namespace Yau.NodeProofs

theorem U02_proved : Yau.Blueprint.U02 := U02_of_originalU01 U01_proved

theorem U02_contract_proved : Yau.BlueprintContracts.U02_contract := U02_proved

end Yau.NodeProofs
