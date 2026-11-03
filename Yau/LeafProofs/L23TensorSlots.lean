import Yau.LeafProofs.L23TensorAlgebra

/-! Curvature acts on every covariant slot, including derivative slots. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def tensorSlotAction (s : Fin r) (D : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) : ℝ :=
  ∑ b : ι, D b (v s) * A (Function.update v s b)

def tensorConnectionAction (D : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) : ℝ :=
  ∑ s : Fin r, tensorSlotAction s D A v

theorem tensorConnectionAction_sub_tensor (D : Matrix ι ι ℝ)
    (A B : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorConnectionAction D (fun w => A w-B w) v =
      tensorConnectionAction D A v-tensorConnectionAction D B v := by
  simp only [tensorConnectionAction,tensorSlotAction,mul_sub,Finset.sum_sub_distrib]

theorem tensorConnectionAction_sub_matrix (D E : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorConnectionAction (D-E) A v =
      tensorConnectionAction D A v-tensorConnectionAction E A v := by
  simp only [tensorConnectionAction,tensorSlotAction,Matrix.sub_apply,
    sub_mul,Finset.sum_sub_distrib]

theorem tensorConnectionAction_add_matrix (D E : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorConnectionAction (D+E) A v =
      tensorConnectionAction D A v+tensorConnectionAction E A v := by
  simp only [tensorConnectionAction,tensorSlotAction,Matrix.add_apply,
    add_mul,Finset.sum_add_distrib]

theorem tensorSlotAction_commute {s t : Fin r} (hst : s ≠ t)
    (D E : Matrix ι ι ℝ) (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorSlotAction s D (tensorSlotAction t E A) v =
      tensorSlotAction t E (tensorSlotAction s D A) v := by
  unfold tensorSlotAction
  simp only [Function.update_of_ne hst, Function.update_of_ne hst.symm,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [Function.update_comm hst]
  ring

theorem tensorSlotAction_comp_same (s : Fin r) (D E : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorSlotAction s D (tensorSlotAction s E A) v =
      tensorSlotAction s (E*D) A v := by
  unfold tensorSlotAction
  simp only [Function.update_self, Function.update_idem, Finset.mul_sum,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem tensorSlotAction_sub_matrix (s : Fin r) (D E : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorSlotAction s (D-E) A v = tensorSlotAction s D A v - tensorSlotAction s E A v := by
  simp only [tensorSlotAction, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem tensorSlotAction_sum {κ : Type*} [Fintype κ] (s : Fin r) (D : Matrix ι ι ℝ)
    (A : κ → (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorSlotAction s D (fun w => ∑ k, A k w) v = ∑ k, tensorSlotAction s D (A k) v := by
  simp only [tensorSlotAction, Finset.mul_sum]
  exact Finset.sum_comm

/-- Operators on distinct slots commute; the diagonal slots produce the matrix commutator. -/
theorem tensorConnectionAction_commutator (D E : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (v : Fin r → ι) :
    tensorConnectionAction D (tensorConnectionAction E A) v -
      tensorConnectionAction E (tensorConnectionAction D A) v =
        tensorConnectionAction (E*D-D*E) A v := by
  have hpoint (s t : Fin r) :
      tensorSlotAction s D (tensorSlotAction t E A) v -
        tensorSlotAction t E (tensorSlotAction s D A) v =
          if s=t then tensorSlotAction s (E*D-D*E) A v else 0 := by
    by_cases hst : s=t
    · subst t
      rw [if_pos rfl, tensorSlotAction_comp_same, tensorSlotAction_comp_same,
        tensorSlotAction_sub_matrix]
    · rw [if_neg hst, tensorSlotAction_commute hst, sub_self]
  unfold tensorConnectionAction
  simp_rw [tensorSlotAction_sum]
  conv_lhs => rhs; rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_sub_distrib]
  simp only [hpoint]
  simp

end Yau.LeafProofs.L23Aux
