import Yau.Proofs.G04MetricNormalization
import Yau.Proofs.G04ClosedHodge
import Yau.Proofs.G04SignedOrderBounds
import Yau.Proofs.G04PaperForms
import Yau.Proofs.G04FlowTarget
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint

theorem hodgeTarget : PaperHodgeNormalizationTarget := by
  intro n M h hs hk
  exact ⟨formCalculus h hs, hodgeNormalization h hs hk, representationBridge h hs,
    traceBridge h hs, scalarLaplacian h hs hk, kahlerLeviForms h hs hk, oneOneNorm h⟩

end Yau.NodeProofs.G04Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem G04_proved : G04 :=
  ⟨G04Aux.metricNormalization, G04Aux.hodgeTarget, G04Aux.flowTarget⟩

theorem G04_contract_proved : Yau.BlueprintContracts.G04_contract := G04_proved

end Yau.NodeProofs
