import Yau.LeafProofs.L23ContractionWordCalculus
import Yau.LeafProofs.L23ContractionWordNorm

/-! The eleven fixed actual quadratic words in the original Q polynomial. -/

noncomputable section

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def baseFreeSlot (i : Fin 4) : SlotLabel 4 := Sum.inl i
def baseSlotA : SlotLabel 4 := Sum.inr (0,0)
def baseSlotB : SlotLabel 4 := Sum.inr (0,1)
def baseSlotP : SlotLabel 4 := Sum.inr (1,0)
def baseSlotQ : SlotLabel 4 := Sum.inr (1,1)

def baseLeftSlots : Fin 11 → Fin 4 → SlotLabel 4 :=
  ![![baseSlotA,baseFreeSlot 3,baseSlotP,baseSlotB],
    ![baseFreeSlot 0,baseFreeSlot 1,baseFreeSlot 2,baseSlotQ],
    ![baseFreeSlot 0,baseFreeSlot 1,baseFreeSlot 3,baseSlotQ],
    ![baseSlotB,baseFreeSlot 0,baseSlotA,baseSlotQ],
    ![baseSlotB,baseFreeSlot 0,baseFreeSlot 1,baseSlotQ],
    ![baseSlotB,baseFreeSlot 0,baseFreeSlot 2,baseSlotQ],
    ![baseSlotB,baseFreeSlot 0,baseFreeSlot 3,baseSlotQ],
    ![baseSlotB,baseFreeSlot 1,baseSlotA,baseSlotQ],
    ![baseSlotB,baseFreeSlot 1,baseFreeSlot 0,baseSlotQ],
    ![baseSlotB,baseFreeSlot 1,baseFreeSlot 2,baseSlotQ],
    ![baseSlotB,baseFreeSlot 1,baseFreeSlot 3,baseSlotQ]]

def baseRightSlots : Fin 11 → Fin 4 → SlotLabel 4 :=
  ![![baseFreeSlot 0,baseFreeSlot 1,baseFreeSlot 2,baseSlotQ],
    ![baseSlotA,baseSlotP,baseFreeSlot 3,baseSlotB],
    ![baseSlotA,baseFreeSlot 2,baseSlotP,baseSlotB],
    ![baseSlotP,baseFreeSlot 1,baseFreeSlot 2,baseFreeSlot 3],
    ![baseSlotA,baseSlotP,baseFreeSlot 2,baseFreeSlot 3],
    ![baseSlotA,baseFreeSlot 1,baseSlotP,baseFreeSlot 3],
    ![baseSlotA,baseFreeSlot 1,baseFreeSlot 2,baseSlotP],
    ![baseSlotP,baseFreeSlot 0,baseFreeSlot 2,baseFreeSlot 3],
    ![baseSlotA,baseSlotP,baseFreeSlot 2,baseFreeSlot 3],
    ![baseSlotA,baseFreeSlot 0,baseSlotP,baseFreeSlot 3],
    ![baseSlotA,baseFreeSlot 0,baseFreeSlot 2,baseSlotP]]

def baseWord (j : Fin 11) : Word2 4 4 4 where
  wire := Equiv.ofBijective (Sum.elim (baseLeftSlots j) (baseRightSlots j)) (by
    fin_cases j <;> decide)

def baseCoeff : Fin 11 → SmallCoeff :=
  ![.negOne,.posHalf,.posHalf,.posHalf,.posHalf,.posHalf,.posHalf,
    .negHalf,.negHalf,.negHalf,.negHalf]

def baseTerms : List (JetTerm 0) := List.ofFn (fun j : Fin 11 =>
  { leftOrder := 0, rightOrder := 0, coeff := baseCoeff j, word := baseWord j })

theorem baseTerms_length : baseTerms.length=11 := by simp [baseTerms]

end Yau.LeafProofs.L23Aux
