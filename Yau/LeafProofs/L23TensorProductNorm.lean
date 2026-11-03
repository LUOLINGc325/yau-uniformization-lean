import Yau.LeafProofs.L23TensorProductCalculus
import Yau.LeafProofs.L23TensorMetricAlgebra

/-! The actual metric contraction of a finite tensor product factors. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r s : ℕ}

theorem sum_tensor_append (f : (Fin (r+s) → ι) → ℝ) :
    (∑ v, f v)=∑ a : Fin r → ι, ∑ b : Fin s → ι, f (Fin.append a b) := by
  calc
    _=∑ q : (Fin r → ι) × (Fin s → ι), f (Fin.append q.1 q.2) :=
      ((Fin.appendEquiv r s).sum_comp f).symm
    _=_ := Fintype.sum_prod_type _

theorem tensorContraction_concatProduct (H : Matrix ι ι ℝ)
    (A A' : (Fin r → ι) → ℝ) (B B' : (Fin s → ι) → ℝ) :
    tensorContraction H (tensorConcatProduct A B) (tensorConcatProduct A' B')=
      tensorContraction H A A'*tensorContraction H B B' := by
  unfold tensorContraction
  rw [sum_tensor_append]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [sum_tensor_append]
  simp only [tensorConcatProduct,Fin.append_left,Fin.append_right,Fin.prod_univ_add,
    Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro b' _
  ring

end Finite

theorem covTensorNormSq_concatProduct {n r s : ℕ}
    (G : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (B : CovTensor n s) :
    covTensorNormSq G (tensorConcatProduct A B)=covTensorNormSq G A*covTensorNormSq G B :=
  tensorContraction_concatProduct G⁻¹ A A B B

end Yau.LeafProofs.L23Aux
