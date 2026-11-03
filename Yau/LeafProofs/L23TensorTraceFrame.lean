import Yau.LeafProofs.L23TensorFrameContraction
import Yau.LeafProofs.L23RicciBound

/-! First-two-slot metric trace and change of tensor frame. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

section Finite
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {r : ℕ}

def tensorMetricTrace (H : Matrix ι ι ℝ) (A : (Fin (r+2) → ι) → ℝ)
    (v : Fin r → ι) : ℝ := ∑ a, ∑ b, H a b*A (Fin.cons a (Fin.cons b v))

theorem tensorFrameTransform_cons (D : Matrix ι κ ℝ) (A : (Fin (r+1) → ι) → ℝ)
    (i : κ) (v : Fin r → κ) :
    tensorFrameTransform D A (Fin.cons i v)=∑ a, D a i*
      tensorFrameTransform D (fun w => A (Fin.cons a w)) v := by
  simp only [tensorFrameTransform,sum_tensor_cons,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem tensorMetricTrace_frameTransform
    (H : Matrix κ κ ℝ) (D : Matrix ι κ ℝ) (A : (Fin (r+2) → ι) → ℝ) :
    tensorMetricTrace H (tensorFrameTransform D A)=
      tensorFrameTransform D (tensorMetricTrace (D*H*Dᵀ) A) := by
  funext v
  have hL : tensorMetricTrace H (tensorFrameTransform D A) v=
      ∑ a, ∑ b, (D*H*Dᵀ) a b*
        tensorFrameTransform D (fun w => A (Fin.cons a (Fin.cons b w))) v := by
    simp only [tensorMetricTrace,tensorFrameTransform_cons,Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext a
      arg 2
      ext i
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hL]
  simp only [tensorFrameTransform,tensorMetricTrace,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro w _
  ring

end Finite

end Yau.LeafProofs.L23Aux
