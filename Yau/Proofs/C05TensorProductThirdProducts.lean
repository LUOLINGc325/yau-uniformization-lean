import Yau.Proofs.C05TensorProductThirdReindex

/-! The frozen second-product terms are actual finite slot permutations. -/
noncomputable section
namespace Yau.Proofs.C05TensorProductThirdAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05QJetBudgetAux Yau.LeafProofs.L23Aux
variable {n r s : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem one_val (r s : ℕ) : (1 : Fin (r+s+1+1)).val = 1 := by
  change 1 % (r+s+1+1) = 1
  exact Nat.mod_eq_of_lt (by omega)

theorem slotsLL_val (i : Fin ((r+1+1)+s)) : (slotsLL r s i).val = i.val := rfl
theorem slotsRR_val (i : Fin (r+(s+1+1))) :
    (slotsRR r s i).val = if i.val<r then i.val+2 else if i.val=r then 0
      else if i.val=r+1 then 1 else i.val := rfl
theorem slotsLR_val (i : Fin ((r+1)+(s+1))) :
    (slotsLR r s i).val = if i.val=0 then 1 else if i.val<r+1 then i.val+1
      else if i.val=r+1 then 0 else i.val := rfl
theorem slotsRL_val (i : Fin ((r+1)+(s+1))) :
    (slotsRL r s i).val = if i.val=0 then 0 else if i.val<r+1 then i.val+1
      else if i.val=r+1 then 1 else i.val := rfl

theorem productLL_reindex (A : CovTensor n (r+1+1)) (B : CovTensor n s) :
    productLL A B = fun v => tensorConcatProduct A B (v ∘ slotsLL r s) := by
  funext v
  unfold productLL tensorConcatProduct
  apply congrArg₂ (· * ·)
  · apply congrArg A
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsLL_val,Fin.val_zero,Fin.val_castAdd,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_succ,Fin.cons_zero,Function.comp_apply]
        apply congrArg v
        apply Fin.ext
        simp only [slotsLL_val,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      · simp only [Fin.cons_succ,Function.comp_apply]
        apply congrArg v
        apply Fin.ext
        simp only [slotsLL_val,Fin.val_castAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
  · apply congrArg B
    funext i
    apply congrArg v
    apply Fin.ext
    simp only [Function.comp_apply,slotsLL_val,Fin.val_natAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
    omega

theorem productRR_reindex (A : CovTensor n r) (B : CovTensor n (s+1+1)) :
    productRR A B = fun v => tensorConcatProduct A B (v ∘ slotsRR r s) := by
  funext v
  unfold productRR tensorConcatProduct
  apply congrArg₂ (· * ·)
  · apply congrArg A
    funext i
    apply congrArg v
    apply Fin.ext
    simp only [Function.comp_apply,slotsRR_val,Fin.val_castAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
    have hi := i.isLt
    split_ifs <;> first | contradiction | omega
  · apply congrArg B
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsRR_val,Fin.val_natAdd,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      split_ifs <;> first | contradiction | omega
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_succ,Fin.cons_zero,Function.comp_apply]
        apply congrArg v
        apply Fin.ext
        simp only [slotsRR_val,Fin.val_natAdd,Fin.val_succ,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
        split_ifs <;> first | contradiction | omega
      · simp only [Fin.cons_succ,Function.comp_apply]
        apply congrArg v
        apply Fin.ext
        simp only [slotsRR_val,Fin.val_natAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
        split_ifs <;> first | contradiction | omega

theorem productLR_reindex (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) :
    productLR A B = fun v => tensorConcatProduct A B (v ∘ slotsLR r s) := by
  funext v
  unfold productLR tensorConcatProduct
  apply congrArg₂ (· * ·)
  · apply congrArg A
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsLR_val,Fin.val_castAdd,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
    · simp only [Fin.cons_succ,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsLR_val,Fin.val_castAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      have hi := i.isLt
      split_ifs <;> first | contradiction | omega
  · apply congrArg B
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsLR_val,Fin.val_natAdd,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      split_ifs <;> first | contradiction | omega
    · simp only [Fin.cons_succ,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsLR_val,Fin.val_natAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      split_ifs <;> first | contradiction | omega

theorem productRL_reindex (A : CovTensor n (r+1)) (B : CovTensor n (s+1)) :
    productRL A B = fun v => tensorConcatProduct A B (v ∘ slotsRL r s) := by
  funext v
  unfold productRL tensorConcatProduct
  apply congrArg₂ (· * ·)
  · apply congrArg A
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsRL_val,Fin.val_castAdd,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
    · simp only [Fin.cons_succ,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsRL_val,Fin.val_castAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      have hi := i.isLt
      split_ifs <;> first | contradiction | omega
  · apply congrArg B
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsRL_val,Fin.val_natAdd,Fin.val_zero,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      split_ifs <;> first | contradiction | omega
    · simp only [Fin.cons_succ,Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [slotsRL_val,Fin.val_natAdd,Fin.val_succ,one_val,Fin.val_natAdd,Fin.val_castAdd,Fin.val_succ,Fin.val_zero,ite_true,ite_false,zero_add,add_zero]
      split_ifs <;> first | contradiction | omega

end Yau.Proofs.C05TensorProductThirdAux
