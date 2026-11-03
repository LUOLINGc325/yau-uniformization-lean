import Yau.Proofs.F03HermitianBounds
import Yau.Proofs.F03FiniteDyadicBudget

/-! A genuine common finite support bound controls the sum of the actual Hermitian errors. -/
noncomputable section
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem hermAbsLE_adjacent_sum (q : ℕ) (S : Finset ℕ) (A : ℕ → Herm n) (G : Herm n)
    (hG : G.PosSemidef) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ j ∈ S,HermAbsLE (A j) G B)
    (hTail : ∀ j ∈ S,j+1 < q ∨ q+1 < j → A j=0) :
    HermAbsLE (∑ j ∈ S,A j) G (3*B) := by
  classical
  have hEq : (∑ j ∈ S.filter (fun j => q ≤ j+1 ∧ j ≤ q+1),A j)=∑ j ∈ S,A j := by
    apply Finset.sum_filter_of_ne
    intro j hj hNotZero
    by_contra h
    exact hNotZero (hTail j hj (by omega))
  rw [← hEq]
  apply hermAbsLE_mono hG (hermAbsLE_sum _ A G (fun _ => B)
    (fun j hj => hA j (Finset.mem_filter.mp hj).1))
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast adjacent_nat_band_card q S) hB

end Yau.Proofs.F03Aux
