import Yau.Proofs.P03InjectiveImmersion
import Yau.Proofs.P03FieldGeneration

noncomputable section

namespace Yau.NodeProofs

/-- All four original finite interpolation conclusions, with the native
scalar and field jets, one injective immersion, and one global spanning tuple. -/
theorem P03_proved : Yau.Blueprint.P03 := by
  intro n X
  exact ⟨P03Aux.scalar_finite_interpolation X, P03Aux.field_finite_interpolation X,
    P03Aux.finite_holomorphic_injective_immersion X, P03Aux.field_finite_generation X⟩

theorem P03_contract_proved : Yau.BlueprintContracts.P03_contract := P03_proved

end Yau.NodeProofs
