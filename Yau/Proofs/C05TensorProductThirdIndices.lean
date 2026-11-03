import Yau.Proofs.C05QJetBudgetProduct
import Yau.LeafProofs.L23TensorReindexNorm

/-! Genuine slot equivalences for the four actual second product terms. -/
noncomputable section
namespace Yau.Proofs.C05TensorProductThirdAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05QJetBudgetAux Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def rankSlots {r s : ℕ} (h : r = s) : Fin r ≃ Fin s where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv _ := rfl
  right_inv _ := rfl

def rightTwoMap (r s : ℕ) (i : Fin (r+s+1+1)) : Fin (r+s+1+1) :=
  ⟨if i.val < r then i.val+2 else if i.val=r then 0 else if i.val=r+1 then 1 else i.val,
    by split_ifs <;> have hi := i.isLt <;> omega⟩

theorem rightTwoMap_injective (r s : ℕ) : Function.Injective (rightTwoMap r s) := by
  intro a b hab
  have H := congrArg Fin.val hab
  dsimp only [rightTwoMap] at H
  split_ifs at H <;> apply Fin.ext <;> omega

def rightTwoPerm (r s : ℕ) : Equiv.Perm (Fin (r+s+1+1)) :=
  Equiv.ofBijective (rightTwoMap r s) ((Finite.injective_iff_bijective).mp (rightTwoMap_injective r s))

def mixedMap (flip : Bool) (r s : ℕ) (i : Fin (r+s+1+1)) : Fin (r+s+1+1) :=
  ⟨if i.val=0 then (if flip then 1 else 0) else if i.val<r+1 then i.val+1
    else if i.val=r+1 then (if flip then 0 else 1) else i.val,
    by split_ifs <;> have hi := i.isLt <;> omega⟩

theorem mixedMap_injective (flip : Bool) (r s : ℕ) : Function.Injective (mixedMap flip r s) := by
  intro a b hab
  have H := congrArg Fin.val hab
  dsimp only [mixedMap] at H
  cases flip <;> simp only [Bool.false_eq_true,ite_false,ite_true] at H <;>
    split_ifs at H <;> apply Fin.ext <;> omega

def mixedPerm (flip : Bool) (r s : ℕ) : Equiv.Perm (Fin (r+s+1+1)) :=
  Equiv.ofBijective (mixedMap flip r s) ((Finite.injective_iff_bijective).mp (mixedMap_injective flip r s))

def slotsLL (r s : ℕ) : Fin ((r+1+1)+s) ≃ Fin (r+s+1+1) := rankSlots (by omega)
def slotsRR (r s : ℕ) : Fin (r+(s+1+1)) ≃ Fin (r+s+1+1) :=
  (rankSlots (by omega)).trans (rightTwoPerm r s)
def slotsLR (r s : ℕ) : Fin ((r+1)+(s+1)) ≃ Fin (r+s+1+1) :=
  (rankSlots (by omega)).trans (mixedPerm true r s)
def slotsRL (r s : ℕ) : Fin ((r+1)+(s+1)) ≃ Fin (r+s+1+1) :=
  (rankSlots (by omega)).trans (mixedPerm false r s)

end Yau.Proofs.C05TensorProductThirdAux
