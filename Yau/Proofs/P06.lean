import Yau.Proofs.P06HodgeCutoffConstruction
import Yau.Proofs.P06FinalAssembly
import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.NodeProofs
open Yau Yau.Blueprint

theorem P06_proved : P06 :=
  P06Aux.FinalAssembly.p06_of_cutoffConstructions P06_cutoff_construction_proved

theorem P06_contract_proved : Yau.BlueprintContracts.P06_contract := P06_proved

end Yau.NodeProofs
