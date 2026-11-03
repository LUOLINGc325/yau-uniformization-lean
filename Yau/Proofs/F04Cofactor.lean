import Mathlib

/-! The scalar cofactor estimate after simultaneous metric diagonalization. -/

open scoped BigOperators

namespace Yau.F04Proof

theorem cofactor_eigenvalue_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eigen : ι → ℝ) (heigen0 : ∀ i, 0 < eigen i) (heigen1 : ∀ i, eigen i ≤ 1) :
    (∏ i, eigen i) * (∑ i, (eigen i)⁻¹) ≤ Fintype.card ι := by
  rw [Finset.mul_sum]
  calc
    ∑ i, (∏ j, eigen j) * (eigen i)⁻¹ = ∑ i, ∏ j ∈ Finset.univ.erase i, eigen j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_prod_erase Finset.univ eigen (Finset.mem_univ i)]
      field_simp [ne_of_gt (heigen0 i)]
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.prod_le_one₀ (fun j _ => (heigen0 j).le) (fun j _ => heigen1 j)
    _ = Fintype.card ι := by simp

end Yau.F04Proof
