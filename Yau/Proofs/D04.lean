import Yau.Proofs.D04CoordinateBridge
import Yau.Proofs.D04AtlasGlue
import spec.CHAIN.CONTRACTS

noncomputable section

namespace Yau.NodeProofs

/-- The original manifold compactness theorem, with its original metric,
volume, exhaustion, EReal limit, Hartogs bound and lower-anchor clauses. -/
theorem D04_proved : Yau.Blueprint.D04 := by
  intro n M g hg μ hμ
  exact Yau.Proofs.D04AtlasGlueAux.manifold_bridge_of_coordinate_bridge
    (Yau.Proofs.D04Aux.coordinate_psh_compactness n) M g hg μ hμ

theorem D04_contract_proved : Yau.BlueprintContracts.D04_contract := D04_proved

end Yau.NodeProofs
