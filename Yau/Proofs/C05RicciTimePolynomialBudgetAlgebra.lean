import Yau.Proofs.C05SingleTraceJetBounds
import Yau.Proofs.C05MatrixTensorContraction

/-! Finite metric contractions controlling the three scalar time polynomials. -/
noncomputable section
open scoped Matrix
namespace Yau.Proofs.C05RicciTimePolynomialBudgetAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def matrixProductTraceWord : SingleTraceWord 4 2 where
  toFun := ![Sum.inr 0, Sum.inl 0, Sum.inl 1, Sum.inr 1]
  invFun := Sum.elim (fun p => if p = 0 then 1 else 2)
    (fun j => if j = 0 then 0 else 3)
  left_inv j := by fin_cases j <;> rfl
  right_inv s := by cases s with
    | inl p => fin_cases p <;> rfl
    | inr j => fin_cases j <;> rfl

theorem matrix_product_eq_singleTrace (G A B : Matrix (RIdx n) (RIdx n) ℝ) :
    matrixCovTensor (A * G⁻¹ * B) = singleTraceEval matrixProductTraceWord G⁻¹
      (tensorConcatProduct (matrixCovTensor A) (matrixCovTensor B)) := by
  funext v
  have ht (a b : RIdx n) :
      (fun j => Sum.elim ![a,b] v (matrixProductTraceWord j)) = ![v 0,a,b,v 1] := by
    funext j
    fin_cases j <;> rfl
  simp only [singleTraceEval, ht]
  change (A * G⁻¹ * B) (v 0) (v 1) = ∑ a, ∑ b, G⁻¹ a b * (A (v 0) a * B b (v 1))
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem metricTensorNorm_matrix_product_le (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) :
    metricTensorNorm G (matrixCovTensor (A * G⁻¹ * B)) ≤
      Real.sqrt (2*n:ℕ) * metricTensorNorm G (matrixCovTensor A) *
        metricTensorNorm G (matrixCovTensor B) := by
  rw [matrix_product_eq_singleTrace]
  exact (metricTensorNorm_singleTraceEval_le matrixProductTraceWord G hG _).trans_eq
    (by rw [metricTensorNorm_concatProduct G hG]; ring)

theorem metricTensorNorm_matrix_transpose (G A : Matrix (RIdx n) (RIdx n) ℝ) :
    metricTensorNorm G (matrixCovTensor Aᵀ) = metricTensorNorm G (matrixCovTensor A) := by
  have he : matrixCovTensor Aᵀ =
      fun v => matrixCovTensor A (v ∘ Equiv.swap (0 : Fin 2) 1) := by
    funext v
    simp [matrixCovTensor, Function.comp_def]
  rw [he]
  unfold metricTensorNorm
  rw [covTensorNormSq_reindex]

theorem covTensorPair_matrix_transpose (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.IsSymm) :
    covTensorPair G (matrixCovTensor A) (matrixCovTensor B) =
      (G⁻¹ * A * G⁻¹ * Bᵀ).trace := by
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
  have ht : (G⁻¹ * A * G⁻¹ * Bᵀ).trace =
      ∑ c, ∑ b, ∑ a, ∑ d, G⁻¹ c a * A a b * G⁻¹ b d * B c d := by
    have hassoc : G⁻¹ * A * G⁻¹ * Bᵀ = (G⁻¹ * A) * (G⁻¹ * Bᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hassoc]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.mul_sum, mul_assoc]
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
  rw [hG.inv.apply c a]
  ring

theorem trace_pair_abs_le (G A B : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    |(G⁻¹ * A * G⁻¹ * B).trace| ≤
      metricTensorNorm G (matrixCovTensor A) * metricTensorNorm G (matrixCovTensor B) := by
  have hs : G.IsSymm := by
    change Gᵀ = G
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.isHermitian.eq
  have hh := covTensorPair_abs_le_norm G hG (matrixCovTensor A) (matrixCovTensor Bᵀ)
  rw [covTensorPair_matrix_transpose G A Bᵀ hs, Matrix.transpose_transpose,
    metricTensorNorm_matrix_transpose] at hh
  exact hh

theorem trace_cubic_abs_le (G A H : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    |(G⁻¹ * A * G⁻¹ * A * G⁻¹ * H).trace| ≤
      Real.sqrt (2*n:ℕ) * metricTensorNorm G (matrixCovTensor A) ^ 2 *
        metricTensorNorm G (matrixCovTensor H) := by
  have hh := trace_pair_abs_le G (A * G⁻¹ * A) H hG
  have hp := metricTensorNorm_matrix_product_le G A A hG
  have hn := metricTensorNorm_nonneg G (matrixCovTensor H)
  calc
    _ ≤ metricTensorNorm G (matrixCovTensor (A * G⁻¹ * A)) *
        metricTensorNorm G (matrixCovTensor H) := by simpa only [Matrix.mul_assoc] using hh
    _ ≤ _ := (mul_le_mul_of_nonneg_right hp hn).trans_eq (by ring)

theorem trace_square_abs_le (G H : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    |(G⁻¹ * H * G⁻¹ * H).trace| ≤ metricTensorNorm G (matrixCovTensor H) ^ 2 := by
  simpa only [pow_two] using trace_pair_abs_le G H H hG

theorem trace_quartic_abs_le (G A : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) :
    |(G⁻¹ * A * G⁻¹ * A * G⁻¹ * A * G⁻¹ * A).trace| ≤
      (2*n:ℕ) * metricTensorNorm G (matrixCovTensor A) ^ 4 := by
  have hh := trace_pair_abs_le G (A * G⁻¹ * A) (A * G⁻¹ * A) hG
  have hp := metricTensorNorm_matrix_product_le G A A hG
  have hn := metricTensorNorm_nonneg G (matrixCovTensor (A * G⁻¹ * A))
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ (2*n:ℕ) by positivity)
  calc
    _ ≤ metricTensorNorm G (matrixCovTensor (A * G⁻¹ * A)) ^ 2 := by
      simpa only [Matrix.mul_assoc, pow_two] using hh
    _ ≤ (Real.sqrt (2*n:ℕ) * metricTensorNorm G (matrixCovTensor A) *
        metricTensorNorm G (matrixCovTensor A)) ^ 2 := pow_le_pow_left₀ hn hp 2
    _ = _ := by rw [mul_pow, mul_pow, hs]; ring

end Yau.Proofs.C05RicciTimePolynomialBudgetAux
