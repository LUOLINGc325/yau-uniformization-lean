import Yau.LeafProofs.L23ContractionWordLifts

/-! Explicit bijective wirings for the three correction families in the
actual arbitrary-rank Ricci-flow recurrence. -/

noncomputable section

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def correctionZeroTo (r : ℕ) : (Fin 4 ⊕ Fin (r+1)) → SlotLabel (r+1)
  | .inl j => ![Sum.inr (0,0),Sum.inl 0,Sum.inr (1,1),Sum.inr (0,1)] j
  | .inr j => Fin.cases (Sum.inr (1,0)) (fun j => Sum.inl j.succ) j

def correctionZeroInv (r : ℕ) : SlotLabel (r+1) → (Fin 4 ⊕ Fin (r+1))
  | .inl j => Fin.cases (Sum.inl 1) (fun j => Sum.inr j.succ) j
  | .inr p => ![![Sum.inl 0,Sum.inl 3],![Sum.inr 0,Sum.inl 2]] p.1 p.2

def correctionWord0 (r : ℕ) : Word2 4 (r+1) (r+1) where
  wire :=
    { toFun := correctionZeroTo r
      invFun := correctionZeroInv r
      left_inv := by
        intro v
        cases v with
        | inl j => fin_cases j <;> rfl
        | inr j => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      right_inv := by
        intro v
        cases v with
        | inl j => refine Fin.cases ?_ (fun j => ?_) j <;> rfl
        | inr p => rcases p with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> rfl }

def correctionOneTo {r : ℕ} (s : Fin r) : (Fin 4 ⊕ Fin (r+1)) → SlotLabel (r+1)
  | .inl j => ![Sum.inl 0,Sum.inr (0,0),Sum.inl s.succ,Sum.inr (1,1)] j
  | .inr j => Fin.cases (Sum.inr (0,1))
      (fun j => if j=s then Sum.inr (1,0) else Sum.inl j.succ) j

def correctionOneInv {r : ℕ} (s : Fin r) : SlotLabel (r+1) → (Fin 4 ⊕ Fin (r+1))
  | .inl j => Fin.cases (Sum.inl 0)
      (fun j => if j=s then Sum.inl 2 else Sum.inr j.succ) j
  | .inr p => ![![Sum.inl 1,Sum.inr 0],![Sum.inr s.succ,Sum.inl 3]] p.1 p.2

def correctionWord1 {r : ℕ} (s : Fin r) : Word2 4 (r+1) (r+1) where
  wire :=
    { toFun := correctionOneTo s
      invFun := correctionOneInv s
      left_inv := by
        intro v
        cases v with
        | inl j => fin_cases j <;> simp [correctionOneTo,correctionOneInv]
        | inr j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · by_cases hjs : j=s
              · subst j; simp [correctionOneTo,correctionOneInv]
              · simp [correctionOneTo,correctionOneInv,hjs]
      right_inv := by
        intro v
        cases v with
        | inl j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · by_cases hjs : j=s
              · subst j; simp [correctionOneTo,correctionOneInv]
              · simp [correctionOneTo,correctionOneInv,hjs]
        | inr p =>
            rcases p with ⟨i,j⟩
            fin_cases i <;> fin_cases j <;> simp [correctionOneTo,correctionOneInv] }

def correctionTwoTo {r : ℕ} (s : Fin r) : (Fin 5 ⊕ Fin r) → SlotLabel (r+1)
  | .inl j => ![Sum.inl 0,Sum.inr (0,0),Sum.inl s.succ,Sum.inr (1,1),Sum.inr (0,1)] j
  | .inr j => if j=s then Sum.inr (1,0) else Sum.inl j.succ

def correctionTwoInv {r : ℕ} (s : Fin r) : SlotLabel (r+1) → (Fin 5 ⊕ Fin r)
  | .inl j => Fin.cases (Sum.inl 0)
      (fun j => if j=s then Sum.inl 2 else Sum.inr j) j
  | .inr p => ![![Sum.inl 1,Sum.inl 4],![Sum.inr s,Sum.inl 3]] p.1 p.2

def correctionWord2 {r : ℕ} (s : Fin r) : Word2 5 r (r+1) where
  wire :=
    { toFun := correctionTwoTo s
      invFun := correctionTwoInv s
      left_inv := by
        intro v
        cases v with
        | inl j => fin_cases j <;> simp [correctionTwoTo,correctionTwoInv]
        | inr j =>
            by_cases hjs : j=s
            · subst j; simp [correctionTwoTo,correctionTwoInv]
            · simp [correctionTwoTo,correctionTwoInv,hjs]
      right_inv := by
        intro v
        cases v with
        | inl j =>
            refine Fin.cases ?_ (fun j => ?_) j
            · rfl
            · by_cases hjs : j=s
              · subst j; simp [correctionTwoTo,correctionTwoInv]
              · simp [correctionTwoTo,correctionTwoInv,hjs]
        | inr p =>
            rcases p with ⟨i,j⟩
            fin_cases i <;> fin_cases j <;> simp [correctionTwoTo,correctionTwoInv] }

end Yau.LeafProofs.L23Aux
