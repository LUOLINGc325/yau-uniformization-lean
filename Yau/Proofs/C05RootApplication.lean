import Yau.Proofs.C05
import Yau.Proofs.F01AActualGlobalCore
import Yau.Proofs.F04RootApplication
import Yau.Proofs.C01RootApplication
import Yau.Proofs.C04RootApplication

noncomputable section
namespace Yau.NodeProofs

/-- Apply the original C05 step to its four proved original predecessors. -/
theorem C05_proved : Yau.Blueprint.C05 :=
  (Yau.Proofs.C05Aux.C05_step_proved
    F01_actual_proved F04_proved C01_proved C04_proved).2

theorem C05_contract_proved : Yau.BlueprintContracts.C05_contract := C05_proved

end Yau.NodeProofs
