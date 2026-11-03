import Yau.Proofs.C06RealLiouville
import spec.CHAIN.CONTRACTS

noncomputable section

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.BlueprintContracts

/-- The full original extended-real conclusion, including the constant bottom function. -/
theorem pshLiouville (n : ℕ) (X : KahlerManifold n) : PshLiouville X := by
  intro u hu hB
  obtain ⟨B, hB⟩ := hB
  apply eq_of_lowerTrunc_eq hu.1
  intro j
  apply real_psh_constant X (isPsh_lowerTrunc hu j)
  intro x
  exact D04Aux.lowerTrunc_le j ((hB x).trans
    (EReal.coe_le_coe_iff.mpr (le_max_left B (-(j : ℝ))))) (le_max_right _ _)

theorem C06_proved : C06 := pshLiouville

/-- The frozen predecessor-only interface; the paper's static argument needs no extra input. -/
theorem C06_contract_proved (_hC01 : C01_contract) (_hC04 : C04_contract) : C06_contract :=
  C06_proved

end Yau.Proofs.C06Aux
