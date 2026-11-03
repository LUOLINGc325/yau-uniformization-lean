import Yau.Proofs.C05InverseDerivativeWord

/-! The actual inverse-matrix time composition has two metric traces.
Its norm budget contains no derivatives or external inverse estimate. -/
noncomputable section
open scoped Topology ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def inverseMatrixCompositionWord : Word2 4 2 2 where
  wire :=
    { toFun := Sum.elim
        ![Sum.inl 0,Sum.inr (0,0),Sum.inr (1,1),Sum.inl 1]
        ![Sum.inr (0,1),Sum.inr (1,0)]
      invFun := Sum.elim ![Sum.inl 0,Sum.inl 3]
        (fun p => if p.1=0 then if p.2=0 then Sum.inl 1 else Sum.inr 0
          else if p.2=0 then Sum.inr 1 else Sum.inl 2)
      left_inv := by
        intro s
        cases s with
        | inl i => fin_cases i <;> rfl
        | inr i => fin_cases i <;> rfl
      right_inv := by
        intro s
        cases s with
        | inl i => fin_cases i <;> rfl
        | inr p => rcases p with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl }

theorem inverseMatrixCompositionWord_eval (H C D : Matrix (RIdx n) (RIdx n) ℝ)
    (v : Fin 2 → RIdx n) :
    inverseMatrixCompositionWord.eval H
      (tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)) (matrixCovTensor D) v =
        matrixCovTensor (C*H*D*H*C) v := by
  have hL (a b c d : RIdx n) : (fun j => Sum.elim v (pairAssignment a b c d)
      (inverseMatrixCompositionWord.wire (Sum.inl j))) = ![v 0,a,d,v 1] := by
    funext j
    fin_cases j <;> rfl
  have hR (a b c d : RIdx n) : (fun j => Sum.elim v (pairAssignment a b c d)
      (inverseMatrixCompositionWord.wire (Sum.inr j))) = ![b,c] := by
    funext j
    fin_cases j <;> rfl
  rw [Word2.eval_quad]
  simp_rw [hL,hR]
  have hp (a d : RIdx n) : tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)
      ![v 0,a,d,v 1] = C (v 0) a * C d (v 1) := rfl
  simp_rw [hp]
  change _ = (C*H*D*H*C) (v 0) (v 1)
  rw [show C*H*D*H*C = (C*H)*(D*(H*C)) by simp only [Matrix.mul_assoc]]
  simp only [Matrix.mul_apply,matrixCovTensor,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem inverseMatrixComposition_norm_le (G C D : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) :
    metricTensorNorm G (matrixCovTensor (C*G⁻¹*D*G⁻¹*C)) ≤
      (2*n:ℕ) * metricTensorNorm G (matrixCovTensor C)^2 * metricTensorNorm G (matrixCovTensor D) := by
  have he : matrixCovTensor (C*G⁻¹*D*G⁻¹*C) = inverseMatrixCompositionWord.eval G⁻¹
      (tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)) (matrixCovTensor D) := by
    funext v
    exact (inverseMatrixCompositionWord_eval G⁻¹ C D v).symm
  rw [he]
  have hb := inverseMatrixCompositionWord.eval_norm_le G hG
    (tensorConcatProduct (matrixCovTensor C) (matrixCovTensor C)) (matrixCovTensor D)
  change metricTensorNorm G _ ≤ (2*n:ℕ) * metricTensorNorm G _ * metricTensorNorm G _ at hb
  rw [metricTensorNorm_concatProduct G hG] at hb
  exact hb.trans_eq (by ring)

theorem loweredInverseTimeMatrix_norm_le (G A B : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) :
    metricTensorNorm G (matrixCovTensor (G*A⁻¹*B*A⁻¹*G)) ≤
      (2*n:ℕ) * metricTensorNorm G (matrixCovTensor (loweredInverseMatrix G A))^2 *
        metricTensorNorm G (matrixCovTensor B) := by
  rw [← loweredInverseMatrix_composition G A B hG.det_pos.ne']
  exact inverseMatrixComposition_norm_le G _ B hG

end Yau.Proofs.C05Aux
