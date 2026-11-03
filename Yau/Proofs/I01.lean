import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs
open Yau Blueprint

/-- The packaged global coordinates give the original manifold's conclusion. -/
theorem I01_proved : Yau.BlueprintContracts.I01_contract := by
  intro n M global out h
  exact h.2

end Yau.NodeProofs
