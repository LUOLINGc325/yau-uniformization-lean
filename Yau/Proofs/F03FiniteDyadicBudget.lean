import Yau.Proofs.F03DyadicScaleBand
import Mathlib.Order.Interval.Finset.Nat

/-! The exact common active band gives a uniform finite-sum budget. -/
noncomputable section
namespace Yau.Proofs.F03Aux

theorem adjacent_nat_band_card (q : ℕ) (S : Finset ℕ) :
    (S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1)).card ≤ 3 := by
  classical
  have hSub : S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1) ⊆ Finset.Icc (q-1) (q+1) := by
    intro j hj
    have hh := (Finset.mem_filter.mp hj).2
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
  exact (Finset.card_le_card hSub).trans (by simp only [Nat.card_Icc];omega)

theorem sum_le_three_of_adjacent_band (q : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hBound : ∀ j ∈ S,f j ≤ B)
    (hTail : ∀ j ∈ S,j+1 < q ∨ q+1 < j → f j=0) :
    (∑ j ∈ S,f j) ≤ 3*B := by
  classical
  have hEq : (∑ j ∈ S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1),f j)=∑ j ∈ S,f j := by
    apply Finset.sum_filter_of_ne
    intro j hj hNotZero
    by_contra h
    exact hNotZero (hTail j hj (by omega))
  rw [← hEq]
  calc
    _ ≤ ∑ _j ∈ S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1),B := by
      apply Finset.sum_le_sum
      intro j hj
      exact hBound j (Finset.mem_filter.mp hj).1
    _ = ((S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1)).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast adjacent_nat_band_card q S) hB

theorem dyadic_firstDerivative_sum_budget {s B : ℝ} (hs : 1 ≤ s) (hB : 0 ≤ B)
    (S : Finset ℕ) (A : ℕ → ℝ)
    (hBound : ∀ j ∈ S,|deriv (dyadicPartition j) s| *A j ≤ B) :
    (∑ j ∈ S,|deriv (dyadicPartition j) s| *A j) ≤ 3*B := by
  obtain ⟨q,hTail⟩ := dyadicPartition_common_active_band hs
  apply sum_le_three_of_adjacent_band q S _ hB hBound
  intro j _ hj
  rw [(hTail j hj).2.1,abs_zero,zero_mul]

theorem dyadic_secondDerivative_sum_budget {s B : ℝ} (hs : 1 ≤ s) (hB : 0 ≤ B)
    (S : Finset ℕ) (A : ℕ → ℝ)
    (hBound : ∀ j ∈ S,|deriv (deriv (dyadicPartition j)) s| *A j ≤ B) :
    (∑ j ∈ S,|deriv (deriv (dyadicPartition j)) s| *A j) ≤ 3*B := by
  obtain ⟨q,hTail⟩ := dyadicPartition_common_active_band hs
  apply sum_le_three_of_adjacent_band q S _ hB hBound
  intro j _ hj
  rw [(hTail j hj).2.2,abs_zero,zero_mul]

end Yau.Proofs.F03Aux
