import Yau.Proofs.C07Original
import Yau.Proofs.C02RootApplication
import Yau.Proofs.C04RootApplication
import Yau.Proofs.C05RootApplication
import Yau.Proofs.C06
import Yau.Proofs.EnvelopeRootApplication

noncomputable section
namespace Yau.NodeProofs

/-- Apply original C07 to its five proved original predecessors. -/
theorem C07_proved : Yau.Blueprint.C07 :=
  Yau.Proofs.C07Aux.C07_of_original_predecessors
    C02_proved C04_proved C05_proved
    Yau.Proofs.C06Aux.C06_proved E03_actual_proved

theorem C07_contract_proved : Yau.BlueprintContracts.C07_contract := C07_proved

end Yau.NodeProofs
