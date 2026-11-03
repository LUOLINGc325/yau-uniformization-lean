import Yau.LeafProofs.L23TensorSlots

/-! Reindexing the metric derivative in every genuine covariant tensor slot. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def tensorContraction (H : Matrix ι ι ℝ) (A B : (Fin r → ι) → ℝ) : ℝ :=
  ∑ v : Fin r → ι, ∑ w : Fin r → ι,
    A v*B w*∏ j : Fin r, H (v j) (w j)

theorem tensorContraction_symm (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A B : (Fin r → ι) → ℝ) : tensorContraction H A B=tensorContraction H B A := by
  unfold tensorContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  have hp : (∏ j : Fin r, H (w j) (v j)) = ∏ j : Fin r, H (v j) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hH.apply (v j) (w j)
  rw [hp]
  ring

theorem tensorContraction_sub_left (H : Matrix ι ι ℝ) (A B C : (Fin r → ι) → ℝ) :
    tensorContraction H (fun v => A v-B v) C =
      tensorContraction H A C-tensorContraction H B C := by
  simp only [tensorContraction,sub_mul,Finset.sum_sub_distrib]

theorem tensorContraction_sub_right (H : Matrix ι ι ℝ) (A B C : (Fin r → ι) → ℝ) :
    tensorContraction H A (fun v => B v-C v) =
      tensorContraction H A B-tensorContraction H A C := by
  simp only [tensorContraction,mul_sub,sub_mul,Finset.sum_sub_distrib]

def tensorSlotSwap (s : Fin r) : ((Fin r → ι) × ι) ≃ ((Fin r → ι) × ι) where
  toFun q := (Function.update q.1 s q.2,q.1 s)
  invFun q := (Function.update q.1 s q.2,q.1 s)
  left_inv q := by
    rcases q with ⟨v,b⟩
    simp only [Function.update_self,Function.update_idem,Function.update_eq_self]
  right_inv q := by
    rcases q with ⟨v,b⟩
    simp only [Function.update_self,Function.update_idem,Function.update_eq_self]

theorem tensorProduct_update_slot (H : Matrix ι ι ℝ) (v w : Fin r → ι)
    (s : Fin r) (b : ι) :
    (∏ j : Fin r, H (Function.update v s b j) (w j)) =
      H b (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j) := by
  rw [←Finset.mul_prod_erase Finset.univ
    (fun j : Fin r => H (Function.update v s b j) (w j)) (Finset.mem_univ s)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem tensorSlotAction_contraction_left (H D : Matrix ι ι ℝ)
    (s : Fin r) (A B : (Fin r → ι) → ℝ) :
    tensorContraction H (tensorSlotAction s D A) B =
      ∑ v : Fin r → ι, ∑ w : Fin r → ι, ∑ b : ι,
        D (v s) b*H b (w s)*A v*B w*∏ j ∈ Finset.univ.erase s, H (v j) (w j) := by
  let f : ((Fin r → ι) × ι) → ℝ := fun q =>
    ∑ w : Fin r → ι, D q.2 (q.1 s)*A (Function.update q.1 s q.2)*B w*
      ∏ j : Fin r, H (q.1 j) (w j)
  have hleft : tensorContraction H (tensorSlotAction s D A) B = ∑ q, f q := by
    unfold tensorContraction tensorSlotAction
    simp only [Finset.sum_mul,Fintype.sum_prod_type,f]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_comm
  rw [hleft,←(tensorSlotSwap (ι := ι) s).sum_comp f]
  rw [Fintype.sum_prod_type]
  unfold f tensorSlotSwap
  simp only [Equiv.coe_fn_mk,Function.update_self,Function.update_idem,
    Function.update_eq_self,tensorProduct_update_slot]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorContraction_connectionAction_left (H D : Matrix ι ι ℝ)
    (A B : (Fin r → ι) → ℝ) :
    tensorContraction H (tensorConnectionAction D A) B =
      ∑ s : Fin r, tensorContraction H (tensorSlotAction s D A) B := by
  unfold tensorContraction tensorConnectionAction
  simp only [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext v
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem tensorSlotMetricAction_left (H D : Matrix ι ι ℝ)
    (s : Fin r) (A B : (Fin r → ι) → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A v*B w*(D*H) (v s) (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j)) =
      tensorContraction H (tensorSlotAction s D A) B := by
  rw [tensorSlotAction_contraction_left]
  simp only [Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorSlotMetricAction_right_self (H D : Matrix ι ι ℝ) (hH : H.IsSymm)
    (s : Fin r) (A : (Fin r → ι) → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A v*A w*(H*Dᵀ) (v s) (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j)) =
      tensorContraction H (tensorSlotAction s D A) A := by
  rw [←tensorSlotMetricAction_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  have hp : (∏ j ∈ Finset.univ.erase s, H (w j) (v j)) =
      ∏ j ∈ Finset.univ.erase s, H (v j) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hH.apply (v j) (w j)
  have hm : (H*Dᵀ) (w s) (v s) = (D*H) (v s) (w s) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [hH.apply b (w s)]
    ring
  rw [hp,hm]
  ring

theorem tensorSlotMetricAction_right (H D : Matrix ι ι ℝ) (hH : H.IsSymm)
    (s : Fin r) (A B : (Fin r → ι) → ℝ) :
    (∑ v : Fin r → ι, ∑ w : Fin r → ι,
      A v*B w*(H*Dᵀ) (v s) (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j)) =
      tensorContraction H A (tensorSlotAction s D B) := by
  rw [tensorContraction_symm H hH A,←tensorSlotMetricAction_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  have hp : (∏ j ∈ Finset.univ.erase s, H (w j) (v j)) =
      ∏ j ∈ Finset.univ.erase s, H (v j) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hH.apply (v j) (w j)
  have hm : (H*Dᵀ) (w s) (v s) = (D*H) (v s) (w s) := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [hH.apply b (w s)]
    ring
  rw [hp,hm]
  ring

theorem tensorContraction_connectionAction_right (H D : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A B : (Fin r → ι) → ℝ) :
    tensorContraction H A (tensorConnectionAction D B) =
      ∑ s : Fin r, tensorContraction H A (tensorSlotAction s D B) := by
  rw [tensorContraction_symm H hH A,tensorContraction_connectionAction_left]
  apply Finset.sum_congr rfl
  intro s _
  exact tensorContraction_symm H hH _ _

def tensorMetricVariation (H J : Matrix ι ι ℝ) (A B : (Fin r → ι) → ℝ) : ℝ :=
  ∑ s : Fin r, ∑ v : Fin r → ι, ∑ w : Fin r → ι,
    A v*B w*J (v s) (w s)*∏ j ∈ Finset.univ.erase s, H (v j) (w j)

theorem tensorMetricVariation_connection (H D : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A : (Fin r → ι) → ℝ) :
    tensorMetricVariation H (-(D*H+H*Dᵀ)) A A =
      -2*tensorContraction H (tensorConnectionAction D A) A := by
  rw [tensorContraction_connectionAction_left]
  unfold tensorMetricVariation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hleft := tensorSlotMetricAction_left H D s A A
  have hright := tensorSlotMetricAction_right_self H D hH s A
  simp only [Matrix.neg_apply,Matrix.add_apply,neg_add,mul_neg,mul_add,
    add_mul,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  linarith

theorem tensorMetricVariation_connection_pair (H D : Matrix ι ι ℝ) (hH : H.IsSymm)
    (A B : (Fin r → ι) → ℝ) :
    tensorMetricVariation H (-(D*H+H*Dᵀ)) A B =
      -tensorContraction H (tensorConnectionAction D A) B-
        tensorContraction H A (tensorConnectionAction D B) := by
  calc
    _ = ∑ s : Fin r, (-tensorContraction H (tensorSlotAction s D A) B-
        tensorContraction H A (tensorSlotAction s D B)) := by
      unfold tensorMetricVariation
      apply Finset.sum_congr rfl
      intro s _
      have hleft := tensorSlotMetricAction_left H D s A B
      have hright := tensorSlotMetricAction_right H D hH s A B
      simp only [Matrix.neg_apply,Matrix.add_apply,neg_add,mul_neg,mul_add,
        add_mul,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]
      linarith
    _ = _ := by
      rw [tensorContraction_connectionAction_left,
        tensorContraction_connectionAction_right H D hH]
      simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib]

end Yau.LeafProofs.L23Aux
