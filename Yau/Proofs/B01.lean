import spec.CHAIN.CONTRACTS
import Yau.Proofs.B01Standard
import Yau.Proofs.B01Cusp
import Yau.Proofs.B01Inverse
import Yau.Proofs.B01Reduction

noncomputable section

namespace Yau.NodeProofs
open Yau.Blueprint Yau.Proofs.B01Aux

theorem B01_proved : B01 := by
  refine ⟨standardDiscRealization, completeDiscMetricRealization, discAreaTransport,
    bundleToEmbeddedReduction, ?_⟩
  intro M r q E _ _ _ _ _ _ _
  exact ⟨imageLocalFrameTransport E, imageMetricTransport E, imageCurvatureTransport E,
    imagePositivityTransport E, imageSectionTransport E, imageBoundTransport E,
    imageIntegralTransport E, sectionTopFormRealization E, topFormSectionRecovery E,
    cutoffSourceFormRealization E, curveWeightedNakanoTransport E,
    cutoffInverseCurvatureBound E, sectionTopFormVolumeTransport E⟩

theorem B01_contract_proved : Yau.BlueprintContracts.B01_contract := B01_proved

end Yau.NodeProofs
