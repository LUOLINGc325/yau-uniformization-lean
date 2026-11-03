import Yau.Proofs.G02GluedVolume

noncomputable section
namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem G02_proved : G02 := by
  intro n M h hsmooth
  obtain ⟨μ, hμ⟩ := Yau.Proofs.G02Aux.exists_riemannianVolume h hsmooth
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact Yau.LeafProofs.L12Aux.riemannianVolume_unique h hν hμ

theorem G02_contract_proved : Yau.BlueprintContracts.G02_contract := G02_proved

end Yau.NodeProofs
