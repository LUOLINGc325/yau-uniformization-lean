import Yau.Proofs.C05RicciInverseTensor

/-! A rank-two covariant pairing is the actual inverse-metric matrix
trace. The two inverse metric factors are retained. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem sum_four_swap_first_third {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ b, ∑ a, ∑ d, f a b c d := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

theorem covTensorPair_matrix (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) (hB : B.IsSymm) :
    covTensorPair G (matrixCovTensor A) (matrixCovTensor B) =
      (G⁻¹ * A * G⁻¹ * B).trace := by
  have h1 : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  have hp : covTensorPair G (matrixCovTensor A) (matrixCovTensor B) =
      ∑ a, ∑ b, ∑ c, ∑ d, A a b * B c d * G⁻¹ a c * G⁻¹ b d := by
    simp only [covTensorPair, matrixCovTensor, sum_tensor_cons, Fin.prod_univ_succ,
      Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ, mul_one, Fintype.sum_unique,
      h1, Fin.cons_succ, Fin.cons_zero]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have ht : (G⁻¹ * A * G⁻¹ * B).trace =
      ∑ c, ∑ b, ∑ a, ∑ d, G⁻¹ c a * A a b * G⁻¹ b d * B d c := by
    have hassoc : G⁻¹ * A * G⁻¹ * B = (G⁻¹ * A) * (G⁻¹ * B) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro c _
    exact Finset.sum_comm
  rw [hp, ht, sum_four_swap_first_third]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [hG.inv.apply c a, hB.apply d c]
  ring

end Yau.Proofs.C05Aux
