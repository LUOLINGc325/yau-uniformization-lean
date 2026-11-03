import Yau.Proofs.E01OptimizerLsc
import Yau.Proofs.E01OriginalGap
import Yau.Proofs.E01OriginalContacts
import spec.CHAIN.CONTRACTS

/-! The original optimizer, volume gap and finite-contact contract in every dimension. -/

noncomputable section
namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem E01_proved : Yau.Blueprint.E01 := by
  intro n X o h U P ρ hloc
  intro T _hT x
  refine ⟨E01Aux.original_ellipsoidLogDet_lowerSemicontinuous hloc T x, ?_⟩
  intro z t hz ht
  obtain ⟨B, hB, huniq⟩ := E01Aux.existsUnique_original_feasible_max hloc T x z t hz ht
  have hgap := E01Aux.original_volumeGap_bounds hloc T x z t hz ht B hB.1 hB.2
  refine ⟨⟨B, hB, huniq⟩, hgap.1, hgap.2, B, hB.1, hB.2, ?_⟩
  intro ε hε
  exact E01Aux.original_max_small_contacts h T x z t hz ht B hB.1 hB.2 ε hε

theorem E01_contract_proved : Yau.BlueprintContracts.E01_contract := E01_proved

end Yau.NodeProofs
