import Yau.Proofs.C02UniformCharts

/-! The original uniform-chart contract follows from its registered
Harnack/completeness and local curvature-derivative parents. -/

noncomputable section
namespace Yau.Proofs

theorem C02
    (hC01 : Yau.BlueprintContracts.C01_contract)
    (hL23 : Yau.LeafObligations.L23) : Yau.BlueprintContracts.C02_contract := by
  intro n X o h U P ρ hloc
  exact Yau.Blueprint.C02Proof.uniformCharts_of_harnackCompleteness hL23
    o h U P ρ hloc (hC01 n X o h U P ρ hloc)

end Yau.Proofs
