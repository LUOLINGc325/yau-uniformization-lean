import Yau.Proofs.E01Congruence

/-! Transport of the exact finite contact identity back to the original fiber coordinates. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem contactRankOne_sum_congruence (S : Herm n) {m : ℕ}
    (η : Fin m → ComplexVector n) (α : Fin m → ℝ) :
    (∑ i, (α i : ℂ) • contactRankOne (matrixFiberMap S (η i))) =
      S * (∑ i, (α i : ℂ) • contactRankOne (η i)) * Sᴴ := by
  simp only [contactRankOne_matrixFiberMap, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem finite_contacts_transport (v : ComplexVector n → EReal)
    (B S : Herm n) (hS : S.IsHermitian) (hSBS : S * B * S = 1)
    (hSS : S * S = B⁻¹) {m : ℕ}
    (η : Fin m → ComplexVector n) (α : Fin m → ℝ) (ε : ℝ)
    (hη : ∀ i, 0 < α i ∧ α i ≤ ε ∧ v (matrixFiberMap S (η i)) = 1 ∧
      ellipsoidQuadratic (1 : Herm n) (η i) = 1)
    (hmatrix : (∑ i, (α i : ℂ) • contactRankOne (η i)) = 1)
    (hsum : ∑ i, α i = n) :
    ∃ ξ : Fin m → ComplexVector n,
      (∀ i, 0 < α i ∧ α i ≤ ε ∧ v (ξ i) = 1 ∧ ellipsoidQuadratic B (ξ i) = 1) ∧
      (∑ i, (α i : ℂ) • contactRankOne (ξ i)) = B⁻¹ ∧ ∑ i, α i = n := by
  refine ⟨fun i => matrixFiberMap S (η i), ?_, ?_, hsum⟩
  · intro i
    refine ⟨(hη i).1, (hη i).2.1, (hη i).2.2.1, ?_⟩
    rw [ellipsoidQuadratic_matrixFiberMap, hS.eq, hSBS]
    exact (hη i).2.2.2
  · rw [contactRankOne_sum_congruence, hmatrix, Matrix.mul_one, hS.eq, hSS]

end Yau.NodeProofs.E01Aux
