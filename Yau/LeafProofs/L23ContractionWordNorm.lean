import Yau.LeafProofs.L23ContractionWordTrace
import Yau.LeafProofs.L23TensorReindexNorm

/-! Every actual two-trace word has norm at most the real dimension
times the product of the original metric tensor norms. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux.Word2
set_option backward.isDefEq.respectTransparency false

variable {n r s q : ℕ}

theorem wiredProduct_normSq (w : Word2 r s q)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (B : CovTensor n s) :
    covTensorNormSq G (w.wiredProduct A B)=covTensorNormSq G A*covTensorNormSq G B := by
  change covTensorNormSq G (fun v => tensorConcatProduct A B (v ∘ w.inputSlotIndex))=_
  rw [covTensorNormSq_reindex,covTensorNormSq_concatProduct]

theorem eval_normSq_le (w : Word2 r s q)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r) (B : CovTensor n s) :
    covTensorNormSq G (w.eval G⁻¹ A B) ≤
      (2*n : ℕ)^2*covTensorNormSq G A*covTensorNormSq G B := by
  rw [eval_eq_two_traces]
  calc
    _≤(2*n : ℕ)*covTensorNormSq G (tensorMetricTrace G⁻¹ (w.wiredProduct A B)) :=
      covTensorNormSq_metricTrace_le G hG _
    _≤(2*n : ℕ)*((2*n : ℕ)*covTensorNormSq G (w.wiredProduct A B)) :=
      mul_le_mul_of_nonneg_left (covTensorNormSq_metricTrace_le G hG _) (Nat.cast_nonneg _)
    _=_ := by rw [wiredProduct_normSq]; push_cast; ring

theorem eval_norm_le (w : Word2 r s q)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r) (B : CovTensor n s) :
    Real.sqrt (covTensorNormSq G (w.eval G⁻¹ A B)) ≤
      (2*n : ℕ)*Real.sqrt (covTensorNormSq G A)*Real.sqrt (covTensorNormSq G B) := by
  have he := eval_normSq_le w G hG A B
  have hA := covTensorNormSq_nonneg G hG A
  have hB := covTensorNormSq_nonneg G hG B
  have hE := covTensorNormSq_nonneg G hG (w.eval G⁻¹ A B)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hE,mul_pow,mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB]
  exact he

end Yau.LeafProofs.L23Aux.Word2
