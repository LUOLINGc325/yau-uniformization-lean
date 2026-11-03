import Yau.Proofs.G01BisectionalNormalization
import Yau.Proofs.G01RicciNormalization
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs
open Yau Blueprint

/-- The original curvature-normalization obligation, from the original smooth Kähler hypotheses alone. -/
theorem G01_proved : PaperCurvatureNormalizationTarget := by
  refine ⟨?_, G01Aux.kahlerRealRicciIdentification, ?_⟩
  · intro n M h hs hk
    exact ⟨G01Aux.paperBisectionalNormalization h hs hk,
      G01Aux.paperRicciChartNormalization h hs hk⟩
  · intro M h hs hk x u v hu hv
    exact G01Aux.paperSurface_normalization h hs hk x u v hu hv

theorem G01_contract_proved : Yau.BlueprintContracts.G01_contract := G01_proved

end Yau.NodeProofs
