import Yau.Proofs.P04Sections

noncomputable section
open scoped Topology Manifold ContDiff

namespace Yau.NodeProofs
open Yau Yau.Proofs.P04Aux

/-- The two original canonical initial-data conclusions, with the actual
canonical norm, Ricci and computed length distance in every dimension. -/
theorem P04_proved : Yau.Blueprint.P04 := by
  intro n X o
  exact canonical_initial_data_from_ancestors X o

theorem P04_contract_proved : Yau.BlueprintContracts.P04_contract := P04_proved

end Yau.NodeProofs
