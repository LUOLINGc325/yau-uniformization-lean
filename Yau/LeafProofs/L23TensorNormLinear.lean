import Yau.LeafProofs.L23TensorAlgebra

/-! Homogeneity and the triangle inequality for the original metric
tensor norm, with no replacement coefficient norm. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem covTensorNormSq_const_mul (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (a : ℝ) :
    covTensorNormSq G (fun v => a*A v)=a^2*covTensorNormSq G A := by
  simp only [covTensorNormSq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem sqrt_covTensorNormSq_const_mul (G : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (a : ℝ) :
    Real.sqrt (covTensorNormSq G (fun v => a*A v))=|a| * Real.sqrt (covTensorNormSq G A) := by
  rw [covTensorNormSq_const_mul,Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq_eq_abs]

theorem covTensorNormSq_add (G : Matrix (RIdx n) (RIdx n) ℝ) (A B : CovTensor n r) :
    covTensorNormSq G (A+B)=covTensorNormSq G A+covTensorPair G A B+
      covTensorPair G B A+covTensorNormSq G B := by
  simp only [covTensorNormSq,covTensorPair,Pi.add_apply,add_mul,mul_add,
    Finset.sum_add_distrib]
  ring

theorem sqrt_covTensorNormSq_add_le (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef)
    (A B : CovTensor n r) :
    Real.sqrt (covTensorNormSq G (A+B)) ≤
      Real.sqrt (covTensorNormSq G A)+Real.sqrt (covTensorNormSq G B) := by
  have hA := covTensorNormSq_nonneg G hG A
  have hB := covTensorNormSq_nonneg G hG B
  have hAB := covTensorNormSq_nonneg G hG (A+B)
  have hp := covTensorPair_le_sqrt G hG A B
  have hq := covTensorPair_le_sqrt G hG B A
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hAB,covTensorNormSq_add]
  nlinarith [Real.sq_sqrt hA,Real.sq_sqrt hB]

theorem sqrt_covTensorNormSq_zero (G : Matrix (RIdx n) (RIdx n) ℝ) :
    Real.sqrt (covTensorNormSq G (0 : CovTensor n r))=0 := by
  simp [covTensorNormSq]

end Yau.LeafProofs.L23Aux
