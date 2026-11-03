import Yau.Proofs.C05InverseMatrixBound
import Yau.Proofs.C05MatrixTensorContraction
import Yau.LeafProofs.L23TensorFrameContraction

/-! An intrinsic coercivity bound controls the actual metric norm of
the lowered inverse, independently of the coordinate frame. -/

noncomputable section
open scoped Matrix

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem matrixCovTensor_frame (D A : Matrix (RIdx n) (RIdx n) ℝ) :
    matrixCovTensor (Dᵀ * A * D) = tensorFrameTransform D (matrixCovTensor A) := by
  funext v
  have h1 : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  simp only [matrixCovTensor, tensorFrameTransform, sum_tensor_cons,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    mul_one, Fintype.sum_unique, h1, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrixCovTensor_euclidean_normSq (A : Matrix (RIdx n) (RIdx n) ℝ) :
    covTensorNormSq (1 : Matrix (RIdx n) (RIdx n) ℝ) (matrixCovTensor A) =
      ∑ a, ∑ b, A a b ^ 2 := by
  have h1 : (1 : Fin 2) = (0 : Fin 1).succ := rfl
  simp only [covTensorNormSq, inv_one, matrixCovTensor, sum_tensor_cons,
    Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.cons_zero, Fin.cons_succ,
    mul_one, Fintype.sum_unique, h1, Fin.cons_succ, Fin.cons_zero]
  simp [Matrix.one_apply, mul_ite, ite_mul, pow_two]

theorem matrix_quadratic_frame (D A : Matrix (RIdx n) (RIdx n) ℝ) (v : RIdx n → ℝ) :
    v ⬝ᵥ ((Dᵀ * A * D) *ᵥ v) = (D *ᵥ v) ⬝ᵥ (A *ᵥ (D *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem loweredInverseMatrix_metric_normSq_bound (G A : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (hA : A.det ≠ 0) (μ : ℝ) (hμ : 0 < μ)
    (hcoercive : ∀ v : RIdx n → ℝ, μ * (v ⬝ᵥ (G *ᵥ v)) ≤ v ⬝ᵥ (A *ᵥ v)) :
    μ ^ 2 * covTensorNormSq G (matrixCovTensor (loweredInverseMatrix G A)) ≤ (2 * n : ℕ) := by
  obtain ⟨D, hD, hGram⟩ := inverseMetric_exists_orthonormal_factor G hG
  have hdetD : D.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hGram
  let B := Dᵀ * A * D
  have hdetB : B.det ≠ 0 := by
    simpa only [B, Matrix.det_mul, Matrix.det_transpose] using
      mul_ne_zero (mul_ne_zero hdetD hA) hdetD
  have hcoB (v : RIdx n → ℝ) : μ * (∑ a, v a ^ 2) ≤ v ⬝ᵥ (B *ᵥ v) := by
    have h := hcoercive (D *ᵥ v)
    have hnorm : (D *ᵥ v) ⬝ᵥ (G *ᵥ (D *ᵥ v)) = ∑ a, v a ^ 2 := by
      rw [← matrix_quadratic_frame, hGram, Matrix.one_mulVec]
      simp only [dotProduct, pow_two]
    rw [hnorm] at h
    rw [matrix_quadratic_frame]
    exact h
  have hframe : Dᵀ * loweredInverseMatrix G A * D = B⁻¹ := by
    have h := loweredInverseMatrix_congruence D G A hdetD
    rw [hGram] at h
    simpa only [loweredInverseMatrix, Matrix.one_mul, Matrix.mul_one] using h.symm
  have hmetric : D * (1 : Matrix (RIdx n) (RIdx n) ℝ)⁻¹ * Dᵀ = G⁻¹ := by
    simpa only [inv_one, Matrix.mul_one] using hD.symm
  have hnorm := covTensorNormSq_frameTransform (1 : Matrix (RIdx n) (RIdx n) ℝ)
    G D hmetric (matrixCovTensor (loweredInverseMatrix G A))
  rw [← matrixCovTensor_frame, hframe, matrixCovTensor_euclidean_normSq] at hnorm
  rw [← hnorm]
  have hb := inverseMatrix_frobenius_sq_bound B hdetB μ hμ hcoB
  rw [Finset.sum_comm] at hb
  simpa only [RIdx, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hb

end Yau.Proofs.C05Aux
