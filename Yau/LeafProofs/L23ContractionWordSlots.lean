import Yau.LeafProofs.L23ContractionWordLifts
import Yau.LeafProofs.L23TensorProductCalculus

/-! The actual finite equivalence from a word's two input tensors to
four leading trace endpoints and its free output slots. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def rankIndexEquiv {r s : ℕ} (e : r=s) : Fin r ≃ Fin s where
  toFun := Fin.cast e
  invFun := Fin.cast e.symm
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Fin.ext; rfl

def pairSlotIndex : PairLabel ≃ Fin 4 := finProdFinEquiv

def wordSlotIndex (q : ℕ) : SlotLabel q ≃ Fin (q+4) :=
  (Equiv.sumComm (Fin q) PairLabel).trans
    ((Equiv.sumCongr pairSlotIndex (Equiv.refl (Fin q))).trans
      (finSumFinEquiv.trans (rankIndexEquiv (Nat.add_comm 4 q))))

theorem wordSlotIndex_free (q : ℕ) (j : Fin q) :
    wordSlotIndex q (Sum.inl j)=j.succ.succ.succ.succ := by
  apply Fin.ext
  change 4+j.val=j.val+1+1+1+1
  omega

theorem wordSlotIndex_pair (q : ℕ) (p : PairLabel) :
    (wordSlotIndex q (Sum.inr p)).val=(pairSlotIndex p).val := rfl

namespace Word2
variable {r s q : ℕ}

def inputSlotIndex (w : Word2 r s q) : Fin (r+s) ≃ Fin (q+4) :=
  finSumFinEquiv.symm.trans (w.wire.trans (wordSlotIndex q))

theorem inputSlotIndex_left (w : Word2 r s q) (j : Fin r) :
    w.inputSlotIndex (Fin.castAdd s j)=wordSlotIndex q (w.wire (Sum.inl j)) := by
  change wordSlotIndex q (w.wire (finSumFinEquiv.symm (Fin.castAdd s j)))=_
  rw [show finSumFinEquiv.symm (Fin.castAdd s j)=Sum.inl j from
    finSumFinEquiv.symm_apply_apply (Sum.inl j)]

theorem inputSlotIndex_right (w : Word2 r s q) (j : Fin s) :
    w.inputSlotIndex (Fin.natAdd r j)=wordSlotIndex q (w.wire (Sum.inr j)) := by
  change wordSlotIndex q (w.wire (finSumFinEquiv.symm (Fin.natAdd r j)))=_
  rw [show finSumFinEquiv.symm (Fin.natAdd r j)=Sum.inr j from
    finSumFinEquiv.symm_apply_apply (Sum.inr j)]

def wiredProduct {ι : Type*} (w : Word2 r s q)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) (v : Fin (q+4) → ι) : ℝ :=
  tensorConcatProduct A B (v ∘ w.inputSlotIndex)

theorem wiredProduct_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Word2 r s q) (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ)
    (v : Fin (q+4) → ι) :
    w.wiredProduct A B v=
      A (fun j => v (wordSlotIndex q (w.wire (Sum.inl j))))*
        B (fun j => v (wordSlotIndex q (w.wire (Sum.inr j)))) := by
  simp only [wiredProduct,tensorConcatProduct,Function.comp_apply,inputSlotIndex_left,inputSlotIndex_right]

end Word2

end Yau.LeafProofs.L23Aux
