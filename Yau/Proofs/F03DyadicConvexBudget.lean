import Yau.Proofs.F03DyadicGluingRegularity
import Yau.Proofs.F03DyadicScaleEstimates

/-! The actual finite dyadic convex combination transfers scale budgets without a number-of-terms loss. -/
noncomputable section
open Set
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem dyadicGluing_finite_partition (u : M.Carrier → ℝ)
    (F : ℕ → M.Carrier → ℝ → ℝ) (x : M.Carrier) (hu : 1 ≤ u x) :
    ∃ N : ℕ,(∑ j ∈ Finset.range (N+1),dyadicPartition j (u x))=1 ∧
      ∀ t : ℝ,dyadicGluing u F x t=
        ∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)*F j x t := by
  obtain ⟨q,_hq,hq'⟩ := exists_nat_pow_near hu (by norm_num : (1:ℝ) < 2)
  refine ⟨q+1,dyadicPartition_sum_one hq'.le,fun t => ?_⟩
  apply dyadicGluing_eq_sum_of_tail
  intro j hj
  cases j with
  | zero => omega
  | succ j =>
    apply dyadicPartition_succ_zero_below
    exact hq'.le.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega))

theorem dyadicGluing_rpow_budget (u : M.Carrier → ℝ)
    (F : ℕ → M.Carrier → ℝ → ℝ) (x : M.Carrier) (hu : 1 ≤ u x)
    (t : ℝ) {B α : ℝ} (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hF : ∀ j : ℕ,dyadicPartition j (u x) ≠ 0 → |F j x t| ≤ B*((2:ℝ)^j)^α) :
    |dyadicGluing u F x t| ≤ B*(2:ℝ)^α*(u x)^α := by
  obtain ⟨N,hN,hSum⟩ := dyadicGluing_finite_partition u F x hu
  rw [hSum t]
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1),|dyadicPartition j (u x)*F j x t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)*(B*(2:ℝ)^α*(u x)^α) := by
      apply Finset.sum_le_sum
      intro j _
      have hc := dyadicPartition_nonnegative j (zero_le_one.trans hu)
      rw [abs_mul,abs_of_nonneg hc]
      by_cases hZero : dyadicPartition j (u x)=0
      · rw [hZero,zero_mul,zero_mul]
      apply mul_le_mul_of_nonneg_left _ hc
      calc
        _ ≤ B*((2:ℝ)^j)^α := hF j hZero
        _ ≤ B*((2:ℝ)^α*(u x)^α) := mul_le_mul_of_nonneg_left
          (dyadicScale_rpow_le hu j (dyadicPartition_scale_support hu j hZero).1 hα) hB
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul,hN,one_mul]

end Yau.Proofs.F03Aux
