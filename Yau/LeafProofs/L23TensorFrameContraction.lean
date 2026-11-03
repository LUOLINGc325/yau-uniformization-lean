import Yau.LeafProofs.L23TensorEvaluation

/-! Finite change-of-frame identities for the actual tensor contractions. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

section Finite
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {r : ℕ}

theorem tensor_contraction_frameTransform
    (H : Matrix κ κ ℝ) (D : Matrix ι κ ℝ) (A B : (Fin r → ι) → ℝ) :
    (∑ v : Fin r → κ, ∑ w : Fin r → κ,
      tensorFrameTransform D A v*tensorFrameTransform D B w*
        ∏ j : Fin r, H (v j) (w j))=
      ∑ a : Fin r → ι, ∑ b : Fin r → ι,
        A a*B b*∏ j : Fin r, (D*H*Dᵀ) (a j) (b j) := by
  classical
  have hp (a b : Fin r → ι) :
      (∑ v : Fin r → κ, ∑ w : Fin r → κ,
        (∏ j, D (a j) (v j))*(∏ j, D (b j) (w j))*∏ j, H (v j) (w j))=
      ∏ j : Fin r, (D*H*Dᵀ) (a j) (b j) := by
    change (∑ v : Fin r → κ, ∑ w : Fin r → κ,
      tensorProduct (fun j => D (a j)) v*tensorProduct (fun j => D (b j)) w*
        ∏ j : Fin r, H (v j) (w j))=_
    rw [product_tensor_contraction]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring
  simp only [tensorFrameTransform,Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext v
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _=A a*B b*∑ v : Fin r → κ, ∑ w : Fin r → κ,
        (∏ j, D (a j) (v j))*(∏ j, D (b j) (w j))*∏ j, H (v j) (w j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _=_ := by rw [hp]

end Finite

theorem covTensorNormSq_frameTransform {n r : ℕ}
    (Gc Gd J : Matrix (RIdx n) (RIdx n) ℝ)
    (hInv : J*Gc⁻¹*Jᵀ=Gd⁻¹) (A : CovTensor n r) :
    covTensorNormSq Gc (tensorFrameTransform J A)=covTensorNormSq Gd A := by
  unfold covTensorNormSq
  rw [tensor_contraction_frameTransform,hInv]

end Yau.LeafProofs.L23Aux
