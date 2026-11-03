import Yau.LeafProofs.L23TensorCalculus

/-! A finite bilinear tensor expression with exactly two metric traces. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux

abbrev PairLabel := Fin 2 × Fin 2
abbrev SlotLabel (q : ℕ) := Fin q ⊕ PairLabel

structure Word2 (r s q : ℕ) where
  wire : (Fin r ⊕ Fin s) ≃ SlotLabel q

namespace Word2
variable {r s q : ℕ}

def eval {ι : Type*} [Fintype ι] (w : Word2 r s q) (H : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (B : (Fin s → ι) → ℝ) (v : Fin q → ι) : ℝ :=
  ∑ a : PairLabel → ι,
    A (fun j => Sum.elim v a (w.wire (Sum.inl j)))*
    B (fun j => Sum.elim v a (w.wire (Sum.inr j)))*
    ∏ p : Fin 2, H (a (p,0)) (a (p,1))

def outputLift : SlotLabel q → SlotLabel (q+1)
  | .inl j => .inl j.succ
  | .inr p => .inr p

def leftInputLift : (Fin r ⊕ Fin s) → (Fin (r+1) ⊕ Fin s)
  | .inl j => .inl j.succ
  | .inr j => .inr j

def dLeftTo (w : Word2 r s q) : (Fin (r+1) ⊕ Fin s) → SlotLabel (q+1)
  | .inl j => Fin.cases (.inl 0) (fun j => outputLift (w.wire (.inl j))) j
  | .inr j => outputLift (w.wire (.inr j))

def dLeftInv (w : Word2 r s q) : SlotLabel (q+1) → (Fin (r+1) ⊕ Fin s)
  | .inl j => Fin.cases (.inl 0) (fun j => leftInputLift (w.wire.symm (.inl j))) j
  | .inr p => leftInputLift (w.wire.symm (.inr p))

theorem dLeftInv_outputLift (w : Word2 r s q) (v : SlotLabel q) :
    dLeftInv w (outputLift v)=leftInputLift (w.wire.symm v) := by
  cases v <;> rfl

theorem dLeftTo_leftInputLift (w : Word2 r s q) (v : Fin r ⊕ Fin s) :
    dLeftTo w (leftInputLift v)=outputLift (w.wire v) := by
  cases v <;> rfl

def dLeft (w : Word2 r s q) : Word2 (r+1) s (q+1) where
  wire :=
    { toFun := dLeftTo w
      invFun := dLeftInv w
      left_inv := by
        intro v
        cases v with
        | inl j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · change dLeftInv w (outputLift (w.wire (.inl j)))=Sum.inl j.succ
              rw [dLeftInv_outputLift,w.wire.symm_apply_apply]
              rfl
        | inr j =>
            change dLeftInv w (outputLift (w.wire (.inr j)))=Sum.inr j
            rw [dLeftInv_outputLift,w.wire.symm_apply_apply]
            rfl
      right_inv := by
        intro v
        cases v with
        | inl j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · change dLeftTo w (leftInputLift (w.wire.symm (.inl j)))=Sum.inl j.succ
              rw [dLeftTo_leftInputLift,w.wire.apply_symm_apply]
              rfl
        | inr p =>
            change dLeftTo w (leftInputLift (w.wire.symm (.inr p)))=Sum.inr p
            rw [dLeftTo_leftInputLift,w.wire.apply_symm_apply]
            rfl }

def rightInputLift : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin (s+1))
  | .inl j => .inl j
  | .inr j => .inr j.succ

def dRightTo (w : Word2 r s q) : (Fin r ⊕ Fin (s+1)) → SlotLabel (q+1)
  | .inl j => outputLift (w.wire (.inl j))
  | .inr j => Fin.cases (.inl 0) (fun j => outputLift (w.wire (.inr j))) j

def dRightInv (w : Word2 r s q) : SlotLabel (q+1) → (Fin r ⊕ Fin (s+1))
  | .inl j => Fin.cases (.inr 0) (fun j => rightInputLift (w.wire.symm (.inl j))) j
  | .inr p => rightInputLift (w.wire.symm (.inr p))

theorem dRightInv_outputLift (w : Word2 r s q) (v : SlotLabel q) :
    dRightInv w (outputLift v)=rightInputLift (w.wire.symm v) := by
  cases v <;> rfl

theorem dRightTo_rightInputLift (w : Word2 r s q) (v : Fin r ⊕ Fin s) :
    dRightTo w (rightInputLift v)=outputLift (w.wire v) := by
  cases v <;> rfl

def dRight (w : Word2 r s q) : Word2 r (s+1) (q+1) where
  wire :=
    { toFun := dRightTo w
      invFun := dRightInv w
      left_inv := by
        intro v
        cases v with
        | inl j =>
            change dRightInv w (outputLift (w.wire (.inl j)))=Sum.inl j
            rw [dRightInv_outputLift,w.wire.symm_apply_apply]
            rfl
        | inr j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · change dRightInv w (outputLift (w.wire (.inr j)))=Sum.inr j.succ
              rw [dRightInv_outputLift,w.wire.symm_apply_apply]
              rfl
      right_inv := by
        intro v
        cases v with
        | inl j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · change dRightTo w (rightInputLift (w.wire.symm (.inl j)))=Sum.inl j.succ
              rw [dRightTo_rightInputLift,w.wire.apply_symm_apply]
              rfl
        | inr p =>
            change dRightTo w (rightInputLift (w.wire.symm (.inr p)))=Sum.inr p
            rw [dRightTo_rightInputLift,w.wire.apply_symm_apply]
            rfl }

end Word2

def castTensor {n r s : ℕ} (e : r=s) (A : CovTensor n r) : CovTensor n s :=
  fun v => A (fun i => v (Fin.cast e i))

theorem castTensor_covariantD {n r s : ℕ} {M : ComplexManifold n} (e : r=s)
    (h : HermitianField M) (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (z : ComplexVector n) :
    covariantD h c (fun w => castTensor e (A w)) z=
      castTensor (congrArg (fun r => r+1) e) (covariantD h c A z) := by
  cases e
  rfl

inductive SmallCoeff
  | negOne | negHalf | posHalf | posOne
  deriving DecidableEq

def SmallCoeff.toReal : SmallCoeff → ℝ
  | .negOne => -1
  | .negHalf => -(1/2)
  | .posHalf => 1/2
  | .posOne => 1

theorem SmallCoeff.abs_toReal_le_one (c : SmallCoeff) : |c.toReal| ≤ 1 := by
  cases c <;> norm_num [SmallCoeff.toReal]

/-- The rank equality follows from the wiring; there is no proposition field. -/
structure JetTerm (k : ℕ) where
  leftOrder : ℕ
  rightOrder : ℕ
  coeff : SmallCoeff
  word : Word2 (4+leftOrder) (4+rightOrder) (4+k)

theorem JetTerm.total {k : ℕ} (e : JetTerm k) : e.leftOrder+e.rightOrder=k := by
  have hc := Fintype.card_congr e.word.wire
  simp only [SlotLabel,PairLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hc
  omega

def JetTerm.dLeft {k : ℕ} (e : JetTerm k) : JetTerm (k+1) where
  leftOrder := e.leftOrder+1
  rightOrder := e.rightOrder
  coeff := e.coeff
  word := e.word.dLeft

def JetTerm.dRight {k : ℕ} (e : JetTerm k) : JetTerm (k+1) where
  leftOrder := e.leftOrder
  rightOrder := e.rightOrder+1
  coeff := e.coeff
  word := e.word.dRight

def reactionTermCount : ℕ → ℕ
  | 0 => 11
  | k+1 => 2*reactionTermCount k+2*k+9

def reactionConstant (n k : ℕ) : ℝ := 1+(2*n : ℕ)*(reactionTermCount k : ℝ)
def jetEvolutionConstant (n k : ℕ) : ℝ := 2*reactionConstant n k+(4+k : ℕ)*(2*n : ℕ)

theorem reactionConstant_pos (n k : ℕ) : 0 < reactionConstant n k := by
  unfold reactionConstant
  positivity

theorem jetEvolutionConstant_pos (n k : ℕ) : 0 < jetEvolutionConstant n k := by
  have hc := reactionConstant_pos n k
  unfold jetEvolutionConstant
  positivity

end Yau.LeafProofs.L23Aux
