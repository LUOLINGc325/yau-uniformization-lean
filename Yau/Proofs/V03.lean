import Yau.Proofs.V03Regularization
import Yau.Proofs.V03Localization
import Yau.Proofs.V03SymbolBounds
import Yau.Proofs.V03ActualEnergyDerivative
import spec.CHAIN.CONTRACTS

/-! The unchanged full original V03 contract, with a₀ = 4. -/

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem v03Contract_proved (X : KahlerManifold n) : V03Contract X := by
  intro q d hd
  refine ⟨initialDiscRegularization hd, localizationEstimates hd, 4, le_rfl, fun a ha => ?_⟩
  exact ⟨symbolBounds hd a ha, fun j => actualEnergyDerivative hd j a ha⟩

theorem v03 : Yau.BlueprintContracts.V03_contract := by
  intro n X
  exact v03Contract_proved X

end Yau.Blueprint.V03Proof
