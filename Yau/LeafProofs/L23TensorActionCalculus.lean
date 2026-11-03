import Yau.LeafProofs.L23CurvatureCalculus

/-! Differentiating the finite all-slot coefficient action. -/

noncomputable section
open scoped Topology ContDiff Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem tensorConnectionAction_neg_matrix (D : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (v : Fin r → RIdx n) :
    tensorConnectionAction (-D) A v=-tensorConnectionAction D A v := by
  simp only [tensorConnectionAction,tensorSlotAction,Matrix.neg_apply,neg_mul,Finset.sum_neg_distrib]

theorem tensorConnectionAction_add_tensor (D : Matrix (RIdx n) (RIdx n) ℝ)
    (A B : CovTensor n r) (v : Fin r → RIdx n) :
    tensorConnectionAction D (fun w => A w+B w) v=
      tensorConnectionAction D A v+tensorConnectionAction D B v := by
  simp only [tensorConnectionAction,tensorSlotAction,mul_add,Finset.sum_add_distrib]

theorem tensorConnectionAction_neg_tensor (D : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (v : Fin r → RIdx n) :
    tensorConnectionAction D (fun w => -A w) v=-tensorConnectionAction D A v := by
  simp only [tensorConnectionAction,tensorSlotAction,mul_neg,Finset.sum_neg_distrib]

theorem tensorConnectionAction_smul_matrix (D : Matrix (RIdx n) (RIdx n) ℝ)
    (A : CovTensor n r) (v : Fin r → RIdx n) (α : ℝ) :
    tensorConnectionAction (α • D) A v=α*tensorConnectionAction D A v := by
  simp only [tensorConnectionAction,tensorSlotAction,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem tensorConnectionAction_sum_matrix {κ : Type*} [Fintype κ]
    (D : κ → Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (v : Fin r → RIdx n) :
    tensorConnectionAction (∑ q, D q) A v=∑ q, tensorConnectionAction (D q) A v := by
  simp only [tensorConnectionAction,tensorSlotAction,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem tensorConnectionAction_sum_tensor {κ : Type*} [Fintype κ]
    (D : Matrix (RIdx n) (RIdx n) ℝ) (A : κ → CovTensor n r) (v : Fin r → RIdx n) :
    tensorConnectionAction D (fun w => ∑ q, A q w) v=
      ∑ q, tensorConnectionAction D (A q) v := by
  simp only [tensorConnectionAction,tensorSlotAction,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem tensorConnectionAction_rDeriv
    (D : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n)
    (hD : ∀ p q, DifferentiableAt ℝ (fun w => D w p q) z)
    (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z) (a : RIdx n) (v : Fin r → RIdx n) :
    rDeriv (fun w => tensorConnectionAction (D w) (A w) v) z a=
      tensorConnectionAction (fun p q => rDeriv (fun w => D w p q) z a) (A z) v+
        tensorConnectionAction (D z) (fun u => rDeriv (fun w => A w u) z a) v := by
  have hterm (s : Fin r) (p : RIdx n) := (hD p (v s)).mul (hA (Function.update v s p))
  have hinner (s : Fin r) : DifferentiableAt ℝ
      (fun w => ∑ p, D w p (v s)*A w (Function.update v s p)) z :=
    DifferentiableAt.fun_sum (fun p _ => hterm s p)
  unfold tensorConnectionAction tensorSlotAction
  calc
    _=∑ s, rDeriv (fun w => ∑ p, D w p (v s)*A w (Function.update v s p)) z a :=
      rDeriv_sum _ hinner a
    _=∑ s, ∑ p, rDeriv (fun w => D w p (v s)*A w (Function.update v s p)) z a := by
      apply Finset.sum_congr rfl
      intro s _
      exact rDeriv_sum _ (fun p => hterm s p) a
    _=∑ s, ∑ p, (rDeriv (fun w => D w p (v s)) z a*A z (Function.update v s p)+
        D z p (v s)*rDeriv (fun w => A w (Function.update v s p)) z a) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro p _
      exact rDeriv_mul (hD p (v s)) (hA _) a
    _=_ := by simp only [Finset.sum_add_distrib]

end Yau.LeafProofs.L23Aux
