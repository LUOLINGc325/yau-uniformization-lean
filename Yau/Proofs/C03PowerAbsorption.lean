import Mathlib

/-! Absorbing the fixed coefficient and exponent in the static distortion
estimate into the single positive constant of the frozen contract. -/

namespace Yau.Proofs.C03Aux

theorem absorb_coefficient_and_exponent (M k : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 0 ≤ A →
      B ≤ M * (1 + A) ^ k → B ≤ C * (1 + A) ^ C := by
  let C := max 1 (max M k)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMC : M ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hkC : k ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro A B hA hB
  have hbase : 1 ≤ 1 + A := by linarith
  calc
    B ≤ M * (1 + A) ^ k := hB
    _ ≤ C * (1 + A) ^ k :=
      mul_le_mul_of_nonneg_right hMC (Real.rpow_nonneg (by linarith) _)
    _ ≤ C * (1 + A) ^ C :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hkC) hC.le

end Yau.Proofs.C03Aux
