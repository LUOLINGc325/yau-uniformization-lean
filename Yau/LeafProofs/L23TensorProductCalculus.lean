import Yau.LeafProofs.L23CovariantReindex

/-! The actual covariant Leibniz rule for finite tensor products. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
open L18Aux
set_option backward.isDefEq.respectTransparency false

theorem update_comp_injective {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (v : β → ι) (f : α → β) (hf : Function.Injective f) (s : α) (b : ι) :
    (Function.update v (f s) b) ∘ f=Function.update (v ∘ f) s b := by
  funext a
  by_cases has : a=s
  · subst a
    simp only [Function.comp_apply,Function.update_self]
  · have he : f a ≠ f s := fun hh => has (hf hh)
    simp only [Function.comp_apply,Function.update_of_ne has,Function.update_of_ne he]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r s : ℕ}

def tensorConcatProduct (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ)
    (v : Fin (r+s) → ι) : ℝ :=
  A (fun j => v (Fin.castAdd s j))*B (fun j => v (Fin.natAdd r j))

theorem tensorConnectionAction_concatProduct (D : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) (v : Fin (r+s) → ι) :
    tensorConnectionAction D (tensorConcatProduct A B) v=
      tensorConcatProduct (tensorConnectionAction D A) B v+
        tensorConcatProduct A (tensorConnectionAction D B) v := by
  have hcross (j : Fin r) (k : Fin s) : Fin.natAdd r k ≠ Fin.castAdd s j := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  have hLL (j : Fin r) (p : ι) :
      (fun k => Function.update v (Fin.castAdd s j) p (Fin.castAdd s k))=
        Function.update (fun k => v (Fin.castAdd s k)) j p :=
    update_comp_injective v _ (Fin.castAdd_injective r s) j p
  have hRR (j : Fin s) (p : ι) :
      (fun k => Function.update v (Fin.natAdd r j) p (Fin.natAdd r k))=
        Function.update (fun k => v (Fin.natAdd r k)) j p := by
    apply update_comp_injective
    intro x y hxy
    apply Fin.ext
    have hv := congrArg Fin.val hxy
    simp only [Fin.val_natAdd] at hv
    omega
  have hLR (j : Fin r) (p : ι) :
      (fun k => Function.update v (Fin.castAdd s j) p (Fin.natAdd r k))=
        (fun k => v (Fin.natAdd r k)) := by
    funext k
    exact Function.update_of_ne (hcross j k) _ _
  have hRL (j : Fin s) (p : ι) :
      (fun k => Function.update v (Fin.natAdd r j) p (Fin.castAdd s k))=
        (fun k => v (Fin.castAdd s k)) := by
    funext k
    exact Function.update_of_ne (Ne.symm (hcross k j)) _ _
  simp only [tensorConnectionAction,tensorSlotAction,tensorConcatProduct]
  rw [Fin.sum_univ_add]
  simp only [hLL,hRR,hLR,hRL,Finset.mul_sum,Finset.sum_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    apply Finset.sum_congr rfl <;> intro p hp <;> ring

variable {n : ℕ} {M : ComplexManifold n}

theorem covariantD_concatProduct_cons (h : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n) (hA : ∀ v, DifferentiableAt ℝ (fun w => A w v) z)
    (hB : ∀ v, DifferentiableAt ℝ (fun w => B w v) z) (i : RIdx n) (v : Fin (r+s) → RIdx n) :
    covariantD h c (fun w => tensorConcatProduct (A w) (B w)) z (Fin.cons i v)=
      tensorConcatProduct (fun u => covariantD h c A z (Fin.cons i u)) (B z) v+
        tensorConcatProduct (A z) (fun u => covariantD h c B z (Fin.cons i u)) v := by
  rw [covariantD_cons,tensorConnectionAction_concatProduct]
  simp only [tensorConcatProduct]
  rw [rDeriv_mul (hA _) (hB _)]
  simp only [covariantD_cons]
  ring

end Yau.LeafProofs.L23Aux
