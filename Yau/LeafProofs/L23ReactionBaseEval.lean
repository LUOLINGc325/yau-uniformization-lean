import Yau.LeafProofs.L23ReactionBaseWords
import Yau.LeafProofs.L23CurvatureEvolution

/-! The fixed finite base words evaluated in the original curvature. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

theorem map_four {α β : Type*} (f : α → β) (a b c d : α) :
    (fun j : Fin 4 => f (![a,b,c,d] j))=![f a,f b,f c,f d] := by
  funext j
  fin_cases j <;> rfl

theorem sum_four_rotate {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)=∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext c
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]

theorem baseWord_eval_quad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : Fin 11) (H : Matrix ι ι ℝ) (R S : (Fin 4 → ι) → ℝ) (v : Fin 4 → ι) :
    (baseWord j).eval H R S v=∑ a, ∑ b, ∑ p, ∑ q,
      R (fun u => Sum.elim v (pairAssignment a b p q) (baseLeftSlots j u))*
        S (fun u => Sum.elim v (pairAssignment a b p q) (baseRightSlots j u))*H a b*H p q := by
  rw [Word2.eval_quad]
  rfl

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_rmTrace (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (i j : RIdx n) :
    realRicciCoeff h c z i j=∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*rmTensor h c z ![a,i,j,b] := rfl

theorem baseWord_zero_eval (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n)
    (i j k l : RIdx n) :
    (baseWord 0).eval (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l]=
      ∑ p, ∑ q, realRicciCoeff h c z l p*(realMetricFn h c z)⁻¹ p q*
        rmTensor h c z ![i,j,k,q] := by
  rw [baseWord_eval_quad]
  simp only [baseLeftSlots,baseRightSlots,Matrix.cons_val_zero,map_four,
    baseFreeSlot,baseSlotA,baseSlotB,baseSlotP,baseSlotQ,
    Sum.elim_inl,Sum.elim_inr,pairAssignment,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  simp_rw [realRicciCoeff_rmTrace]
  simp only [Finset.sum_mul]
  conv_rhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    arg 2
    ext p
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem baseWord_one_eval (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    (baseWord 1).eval (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l]=
      ∑ p, riemannCoeff h c z i j k p*realRicciCoeff h c z p l := by
  rw [baseWord_eval_quad]
  simp only [baseLeftSlots,baseRightSlots,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,map_four,
    baseFreeSlot,baseSlotA,baseSlotB,baseSlotP,baseSlotQ,
    Sum.elim_inl,Sum.elim_inr,pairAssignment]
  simp_rw [riemannCoeff_raise_last h c hz,realRicciCoeff_rmTrace]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs => rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem baseWord_two_eval (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    (baseWord 2).eval (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l]=
      ∑ p, riemannCoeff h c z i j l p*realRicciCoeff h c z k p := by
  rw [baseWord_eval_quad]
  simp only [baseLeftSlots,baseRightSlots,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,map_four,
    baseFreeSlot,baseSlotA,baseSlotB,baseSlotP,baseSlotQ,
    Sum.elim_inl,Sum.elim_inr,pairAssignment]
  simp_rw [riemannCoeff_raise_last h c hz,realRicciCoeff_rmTrace]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs => rw [sum_four_rotate]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem curvatureAction_ricciTensor_two (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (i j k l : RIdx n) :
    curvatureAction h c z i j (ricciTensor h c z) ![k,l]=
      -(∑ p, riemannCoeff h c z i j k p*realRicciCoeff h c z p l)-
        ∑ p, riemannCoeff h c z i j l p*realRicciCoeff h c z k p := by
  simp [curvatureAction,ricciTensor,Fin.sum_univ_succ]
  ring

theorem update_four_zero {ι : Type*} (a b c d p : ι) :
    Function.update ![a,b,c,d] (0 : Fin 4) p=![p,b,c,d] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

theorem update_four_one {ι : Type*} (a b c d p : ι) :
    Function.update ![a,b,c,d] (1 : Fin 4) p=![a,p,c,d] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

theorem update_four_two {ι : Type*} (a b c d p : ι) :
    Function.update ![a,b,c,d] (2 : Fin 4) p=![a,b,p,d] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

theorem update_four_three {ι : Type*} (a b c d p : ι) :
    Function.update ![a,b,c,d] (3 : Fin 4) p=![a,b,c,p] := by
  funext j
  fin_cases j <;> simp [Function.update_apply]

theorem baseWord_firstAction_slot (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) (s : Fin 4) :
    (baseWord ⟨3+s.val,by omega⟩).eval (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l]=
      ∑ a, ∑ b, ∑ p, (realMetricFn h c z)⁻¹ a b*
        riemannCoeff h c z b i (![a,j,k,l] s) p*
          rmTensor h c z (Function.update ![a,j,k,l] s p) := by
  fin_cases s <;> rw [baseWord_eval_quad]
  all_goals
    simp [baseLeftSlots,baseRightSlots,Matrix.cons_val_zero,Matrix.cons_val_succ,map_four,
      baseFreeSlot,baseSlotA,baseSlotB,baseSlotP,baseSlotQ,
      Sum.elim_inl,Sum.elim_inr,pairAssignment,
      update_four_zero,update_four_one,update_four_two,update_four_three]
    simp_rw [riemannCoeff_raise_last h c hz]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring

theorem baseWord_secondAction_slot (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) (s : Fin 4) :
    (baseWord ⟨7+s.val,by omega⟩).eval (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l]=
      ∑ a, ∑ b, ∑ p, (realMetricFn h c z)⁻¹ a b*
        riemannCoeff h c z b j (![a,i,k,l] s) p*
          rmTensor h c z (Function.update ![a,i,k,l] s p) := by
  fin_cases s <;> rw [baseWord_eval_quad]
  all_goals
    simp [baseLeftSlots,baseRightSlots,Matrix.cons_val_zero,Matrix.cons_val_succ,map_four,
      baseFreeSlot,baseSlotA,baseSlotB,baseSlotP,baseSlotQ,
      Sum.elim_inl,Sum.elim_inr,pairAssignment,
      update_four_zero,update_four_one,update_four_two,update_four_three]
    simp_rw [riemannCoeff_raise_last h c hz]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring

theorem baseWord_firstAction_sum (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    (∑ s : Fin 4, (baseWord ⟨3+s.val,by omega⟩).eval
      (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l])=
      -(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        curvatureAction h c z b i (rmTensor h c z) ![a,j,k,l]) := by
  simp_rw [baseWord_firstAction_slot h c hz]
  simp only [curvatureAction,mul_neg,Finset.sum_neg_distrib,neg_neg,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem baseWord_secondAction_sum (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (i j k l : RIdx n) :
    (∑ s : Fin 4, (baseWord ⟨7+s.val,by omega⟩).eval
      (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) ![i,j,k,l])=
      -(∑ a, ∑ b, (realMetricFn h c z)⁻¹ a b*
        curvatureAction h c z b j (rmTensor h c z) ![a,i,k,l]) := by
  simp_rw [baseWord_secondAction_slot h c hz]
  simp only [curvatureAction,mul_neg,Finset.sum_neg_distrib,neg_neg,Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem baseCoeff_sum (f : Fin 11 → ℝ) :
    (∑ j : Fin 11, (baseCoeff j).toReal*f j)=
      -f 0+(1/2 : ℝ)*(f 1+f 2)+
        (1/2 : ℝ)*(∑ s : Fin 4, f ⟨3+s.val,by omega⟩)-
          (1/2 : ℝ)*(∑ s : Fin 4, f ⟨7+s.val,by omega⟩) := by
  simp [Fin.sum_univ_succ,baseCoeff,SmallCoeff.toReal]
  ring

theorem baseWords_sum_eq_rmReaction (h : HermitianField M) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) (v : Fin 4 → RIdx n) :
    (∑ j : Fin 11, (baseCoeff j).toReal*(baseWord j).eval
      (realMetricFn h c z)⁻¹ (rmTensor h c z) (rmTensor h c z) v)=rmReaction h c z v := by
  have hv : v=![v 0,v 1,v 2,v 3] := by funext s; fin_cases s <;> rfl
  rw [hv,baseCoeff_sum,baseWord_zero_eval,baseWord_one_eval h c hz,
    baseWord_two_eval h c hz,baseWord_firstAction_sum h c hz,baseWord_secondAction_sum h c hz]
  simp only [rmReaction,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [curvatureAction_ricciTensor_two]
  simp only [mul_sub,Finset.sum_sub_distrib]
  ring

end Yau.LeafProofs.L23Aux
