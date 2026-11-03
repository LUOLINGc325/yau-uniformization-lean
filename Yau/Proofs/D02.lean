import spec.CHAIN.CONTRACTS
import Yau.Proofs.D02BaseEnclosure
import Yau.Proofs.D02CotangentEnclosure
import Yau.Proofs.D02FiberLimit
import Yau.Proofs.P03InjectiveImmersion

/-! The original four disc-compactness conclusions. The actual original P03
producers supply one injective immersion and one global spanning field tuple;
all compact sets and bounds are chosen before the varying discs. -/

noncomputable section

namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem D02_proved : Yau.Blueprint.D02 := by
  intro n X
  obtain ⟨N, F, hF, hinj, hImm⟩ := P03Aux.finite_holomorphic_injective_immersion X
  obtain ⟨m, V, hV, hspan⟩ := P03Aux.field_finite_generation X
  intro K hK A₀
  have hbase := D02Aux.baseDisc_family_enclosure_of_injective_immersion X hF hImm hinj hK A₀
  have hseq := D02Aux.baseDisc_subsequence_of_injective_immersion X hF hImm hinj hK A₀
  refine ⟨hbase, hseq, fun R => ⟨?_, ?_⟩⟩
  · exact D02Aux.cotangentFamilyEnclosure_of_baseFamilyEnclosure X.metric.form
      (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) hK A₀ R hV hspan hbase
  · exact D02FiberLimitAux.cotangent_sequential_of_base_sequential
      X.metric hK A₀ R V hV hspan hseq

theorem D02_contract_proved : Yau.BlueprintContracts.D02_contract := D02_proved

end Yau.NodeProofs
