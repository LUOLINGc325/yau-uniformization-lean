import Yau.Proofs.G04FlowNormalization
import Yau.Proofs.G04ParabolicNormalization

noncomputable section
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint

theorem flowTarget : PaperFlowNormalizationTarget :=
  ⟨G01Aux.kahlerRealRicciIdentification, flowReal, flowStandardTime, parabolicNormalization⟩

end Yau.NodeProofs.G04Aux
