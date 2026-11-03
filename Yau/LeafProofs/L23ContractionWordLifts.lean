import Yau.LeafProofs.L23ContractionWords

/-! Evaluation of the two actual derivative lifts of a contraction word. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux.Word2
set_option backward.isDefEq.respectTransparency false

variable {r s q : ℕ} {ι : Type*} [Fintype ι]

theorem elim_outputLift (i : ι) (v : Fin q → ι) (a : PairLabel → ι) (j : SlotLabel q) :
    Sum.elim (Fin.cons i v) a (outputLift j)=Sum.elim v a j := by
  cases j <;> rfl

theorem eval_dLeft (w : Word2 r s q) (H : Matrix ι ι ℝ)
    (A : (Fin (r+1) → ι) → ℝ) (B : (Fin s → ι) → ℝ) (i : ι) (v : Fin q → ι) :
    w.dLeft.eval H A B (Fin.cons i v)=w.eval H (fun u => A (Fin.cons i u)) B v := by
  unfold eval
  apply Finset.sum_congr rfl
  intro a _
  have hL : (fun j : Fin (r+1) => Sum.elim (Fin.cons i v) a (w.dLeft.wire (Sum.inl j)))=
      Fin.cons i (fun j => Sum.elim v a (w.wire (Sum.inl j))) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change Sum.elim (Fin.cons i v) a (outputLift (w.wire (Sum.inl j)))=_
      exact elim_outputLift _ _ _ _
  have hR : (fun j : Fin s => Sum.elim (Fin.cons i v) a (w.dLeft.wire (Sum.inr j)))=
      (fun j => Sum.elim v a (w.wire (Sum.inr j))) := by
    funext j
    exact elim_outputLift _ _ _ _
  rw [hL,hR]

theorem eval_dRight (w : Word2 r s q) (H : Matrix ι ι ℝ)
    (A : (Fin r → ι) → ℝ) (B : (Fin (s+1) → ι) → ℝ) (i : ι) (v : Fin q → ι) :
    w.dRight.eval H A B (Fin.cons i v)=w.eval H A (fun u => B (Fin.cons i u)) v := by
  unfold eval
  apply Finset.sum_congr rfl
  intro a _
  have hL : (fun j : Fin r => Sum.elim (Fin.cons i v) a (w.dRight.wire (Sum.inl j)))=
      (fun j => Sum.elim v a (w.wire (Sum.inl j))) := by
    funext j
    exact elim_outputLift _ _ _ _
  have hR : (fun j : Fin (s+1) => Sum.elim (Fin.cons i v) a (w.dRight.wire (Sum.inr j)))=
      Fin.cons i (fun j => Sum.elim v a (w.wire (Sum.inr j))) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change Sum.elim (Fin.cons i v) a (outputLift (w.wire (Sum.inr j)))=_
      exact elim_outputLift _ _ _ _
  rw [hL,hR]

end Yau.LeafProofs.L23Aux.Word2
