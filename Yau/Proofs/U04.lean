import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs
open Yau Blueprint

/-- Package the original map using the surjectivity witness for that same map. -/
theorem U04_proved : Yau.BlueprintContracts.U04_contract := by
  intro n M global out
  exact ⟨rfl, (global.toGlobal out.1).biholomorphic⟩

end Yau.NodeProofs
