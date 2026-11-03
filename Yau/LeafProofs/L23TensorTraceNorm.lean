import Yau.LeafProofs.L23TensorTraceFrame

/-! A single actual inverse-metric trace has squared operator norm at
most the real dimension, proved through the genuine Gram frame. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem tensorMetricTrace_one (A : (Fin (r+2) → ι) → ℝ) (v : Fin r → ι) :
    tensorMetricTrace (1 : Matrix ι ι ℝ) A v=∑ a, A (Fin.cons a (Fin.cons a v)) := by
  simp [tensorMetricTrace,Matrix.one_apply]

theorem tensorMetricTrace_euclidean_sq_le (A : (Fin (r+2) → ι) → ℝ) :
    (∑ v : Fin r → ι, tensorMetricTrace (1 : Matrix ι ι ℝ) A v*
      tensorMetricTrace (1 : Matrix ι ι ℝ) A v) ≤
      (Fintype.card ι : ℝ)*∑ w : Fin (r+2) → ι, A w*A w := by
  have hcs (v : Fin r → ι) : (∑ a, A (Fin.cons a (Fin.cons a v)))^2 ≤
      (Fintype.card ι : ℝ)*∑ a, (A (Fin.cons a (Fin.cons a v)))^2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ => (1 : ℝ)) (fun a => A (Fin.cons a (Fin.cons a v)))
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using hh
  have hdiag : (∑ v : Fin r → ι, ∑ a, (A (Fin.cons a (Fin.cons a v)))^2) ≤
      ∑ w : Fin (r+2) → ι, (A w)^2 := by
    rw [Finset.sum_comm,sum_tensor_cons]
    apply Finset.sum_le_sum
    intro a _
    rw [sum_tensor_cons]
    exact Finset.single_le_sum
      (f := fun b : ι => ∑ v : Fin r → ι, (A (Fin.cons a (Fin.cons b v)))^2)
      (fun b _ => Finset.sum_nonneg (fun v _ => sq_nonneg _)) (Finset.mem_univ a)
  calc
    _=∑ v : Fin r → ι, (∑ a, A (Fin.cons a (Fin.cons a v)))^2 := by
      simp only [tensorMetricTrace_one,pow_two]
    _≤∑ v : Fin r → ι, (Fintype.card ι : ℝ)*∑ a, (A (Fin.cons a (Fin.cons a v)))^2 :=
      Finset.sum_le_sum (fun v _ => hcs v)
    _=(Fintype.card ι : ℝ)*(∑ v : Fin r → ι, ∑ a, (A (Fin.cons a (Fin.cons a v)))^2) := by
      rw [Finset.mul_sum]
    _≤(Fintype.card ι : ℝ)*∑ w : Fin (r+2) → ι, (A w)^2 :=
      mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)
    _=_ := by simp only [pow_two]

end Finite

theorem covTensorNormSq_metricTrace_le {n r : ℕ}
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n (r+2)) :
    covTensorNormSq G (tensorMetricTrace G⁻¹ A) ≤ (2*n : ℕ)*covTensorNormSq G A := by
  obtain ⟨D,hD⟩ := inverseMetric_exists_gram_factor G hG
  have ht := tensorMetricTrace_frameTransform (1 : Matrix (RIdx n) (RIdx n) ℝ) D A
  rw [Matrix.mul_one,←hD] at ht
  unfold covTensorNormSq
  rw [tensor_contraction_eq_frame_sum _ D hD,tensor_contraction_eq_frame_sum _ D hD,←ht]
  simpa only [RIdx,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm] using
    tensorMetricTrace_euclidean_sq_le (tensorFrameTransform D A)

end Yau.LeafProofs.L23Aux
