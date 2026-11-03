import Yau.LeafProofs.L23TensorAlgebra

/-! Tensor evaluation estimates with the original metric contraction. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def tensorProduct (V : Fin r → ι → ℝ) : (Fin r → ι) → ℝ :=
  fun v => ∏ j : Fin r, V j (v j)

def tensorEvaluation (A : (Fin r → ι) → ℝ) (V : Fin r → ι → ℝ) : ℝ :=
  ∑ v : Fin r → ι, A v * tensorProduct V v

theorem separated_tensor_contraction (f : Fin r → ι → ι → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι, ∏ j : Fin r, f j (v j) (w j)) =
      ∏ j : Fin r, ∑ a : ι, ∑ b : ι, f j a b := by
  simp_rw [Fintype.prod_sum]

theorem product_tensor_contraction (H : Matrix ι ι ℝ) (V W : Fin r → ι → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      tensorProduct V v * tensorProduct W w * ∏ j : Fin r, H (v j) (w j)) =
        ∏ j : Fin r, ∑ a : ι, ∑ b : ι, V j a * W j b * H a b := by
  rw [← separated_tensor_contraction]
  simp only [tensorProduct, Finset.prod_mul_distrib]

theorem tensorEvaluation_eq_contraction (G H : Matrix ι ι ℝ) (hHG : H*G=1)
    (A : (Fin r → ι) → ℝ) (V : Fin r → ι → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A v * tensorProduct (fun j => G *ᵥ V j) w * ∏ j : Fin r, H (v j) (w j)) =
        tensorEvaluation A V := by
  have hrow (j : Fin r) (a : ι) : (∑ b, H a b * (G *ᵥ V j) b) = V j a := by
    change (H *ᵥ (G *ᵥ V j)) a = V j a
    rw [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  unfold tensorEvaluation
  apply Finset.sum_congr rfl
  intro v _
  calc
    _ = A v * ∑ w : Fin r → ι, ∏ j : Fin r, H (v j) (w j) * (G *ᵥ V j) (w j) := by
      simp only [Finset.mul_sum, tensorProduct, Finset.prod_mul_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = A v * ∏ j : Fin r, ∑ b, H (v j) b * (G *ᵥ V j) b := by
      rw [Fintype.prod_sum]
    _ = _ := by simp only [hrow, tensorProduct]

theorem product_tensor_metric_norm (G H : Matrix ι ι ℝ) (hHG : H*G=1)
    (V : Fin r → ι → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      tensorProduct (fun j => G *ᵥ V j) v * tensorProduct (fun j => G *ᵥ V j) w *
        ∏ j : Fin r, H (v j) (w j)) =
      ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) := by
  rw [product_tensor_contraction]
  apply Finset.prod_congr rfl
  intro j _
  have hdot (u : ι → ℝ) : (∑ a, ∑ b, u a*u b*H a b) = u ⬝ᵥ (H *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    (∑ a, ∑ b, (G *ᵥ V j) a * (G *ᵥ V j) b * H a b) =
        (G *ᵥ V j) ⬝ᵥ (H *ᵥ (G *ᵥ V j)) := hdot _
    _ = (G *ᵥ V j) ⬝ᵥ V j := by
      rw [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
    _ = V j ⬝ᵥ (G *ᵥ V j) := dotProduct_comm _ _

end Finite

variable {n : ℕ} {r : ℕ}

theorem tensorEvaluation_sq_le (G : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (A : CovTensor n r) (V : Fin r → RIdx n → ℝ) :
    tensorEvaluation A V ^ 2 ≤ covTensorNormSq G A *
      ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) := by
  have hHG : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  have hpair : covTensorPair G A (tensorProduct (fun j => G *ᵥ V j)) =
      tensorEvaluation A V := tensorEvaluation_eq_contraction G G⁻¹ hHG A V
  have hnorm : covTensorNormSq G (tensorProduct (fun j => G *ᵥ V j)) =
      ∏ j : Fin r, V j ⬝ᵥ (G *ᵥ V j) := product_tensor_metric_norm G G⁻¹ hHG V
  have hh := covTensorPair_sq_le G hG A (tensorProduct (fun j => G *ᵥ V j))
  rwa [hpair, hnorm] at hh

end Yau.LeafProofs.L23Aux
