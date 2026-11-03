import Yau.LeafProofs.L23TensorTraceFrame
import Yau.LeafProofs.L23TensorSlots

/-! Every connection slot in a metric trace, including the two contracted
slots, is accounted for by this finite identity. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem tensorConnectionAction_cons (D : Matrix ι ι ℝ)
    (A : (Fin (r+1) → ι) → ℝ) (a : ι) (v : Fin r → ι) :
    tensorConnectionAction D A (Fin.cons a v)=
      (∑ p, D p a*A (Fin.cons p v))+
        tensorConnectionAction D (fun w => A (Fin.cons a w)) v := by
  simp only [tensorConnectionAction,tensorSlotAction,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Fin.update_cons_zero,←Fin.cons_update]

theorem tensorMetricTrace_sub (H : Matrix ι ι ℝ) (A B : (Fin (r+2) → ι) → ℝ)
    (v : Fin r → ι) :
    tensorMetricTrace H (fun w => A w-B w) v=
      tensorMetricTrace H A v-tensorMetricTrace H B v := by
  simp only [tensorMetricTrace,mul_sub,Finset.sum_sub_distrib]

theorem tensorMetricTrace_connectionAction (H D : Matrix ι ι ℝ)
    (A : (Fin (r+2) → ι) → ℝ) (v : Fin r → ι) :
    tensorMetricTrace H (tensorConnectionAction D A) v=
      tensorMetricTrace (D*H+H*Dᵀ) A v+
        tensorConnectionAction D (tensorMetricTrace H A) v := by
  simp only [tensorMetricTrace,tensorConnectionAction_cons,Finset.sum_add_distrib,
    Finset.mul_sum,mul_add]
  have h1 : (∑ a, ∑ b, ∑ p, H a b*(D p a*A (Fin.cons p (Fin.cons b v))))=
      ∑ a, ∑ b, (D*H) a b*A (Fin.cons a (Fin.cons b v)) := by
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h2 : (∑ a, ∑ b, ∑ p, H a b*(D p b*A (Fin.cons a (Fin.cons p v))))=
      ∑ a, ∑ b, (H*Dᵀ) a b*A (Fin.cons a (Fin.cons b v)) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    ring
  have h3 : (∑ a, ∑ b, H a b*tensorConnectionAction D
      (fun w => A (Fin.cons a (Fin.cons b w))) v)=
      tensorConnectionAction D (fun w => tensorMetricTrace H A w) v := by
    simp only [tensorConnectionAction,tensorSlotAction,tensorMetricTrace,Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [h1,h2,h3]
  simp only [Matrix.add_apply,add_mul,Finset.sum_add_distrib]
  ring

end Yau.LeafProofs.L23Aux
