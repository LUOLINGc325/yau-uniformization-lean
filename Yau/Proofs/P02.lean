import Yau.Proofs.P02Classical
import Yau.Proofs.P02Richberg
import Yau.Proofs.P01

noncomputable section
open Filter
open scoped Topology NNReal

namespace Yau.NodeProofs

/-- The original positive-bisectional-curvature weight, with the actual
smooth Levi matrix and linear growth in the computed length distance. -/
theorem P02_proved : Yau.Blueprint.P02 := by
  intro n X o
  obtain ⟨ray,h0,hdist,b,hlim,hlip⟩ := P01_proved n X o
  exact P02Aux.strictPshWeight_of_classical_busemann X o ray b hlim hlip
    (P02Aux.busemann_classicalStrictPsh X o ray h0 hdist b hlim hlip)

theorem P02_contract_proved : Yau.BlueprintContracts.P02_contract := P02_proved

end Yau.NodeProofs
