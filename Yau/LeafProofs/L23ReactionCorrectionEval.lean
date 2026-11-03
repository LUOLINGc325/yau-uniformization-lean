import Yau.LeafProofs.L23ReactionCorrectionWords
import Yau.LeafProofs.L23ContractionWordTrace

/-! The three correction wirings evaluate to the actual finite sums
selected by the all-rank curvature recurrence. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem eval_correctionWord0 (H : Matrix ι ι ℝ)
    (R : (Fin 4 → ι) → ℝ) (B : (Fin (r+1) → ι) → ℝ) (i : ι) (v : Fin r → ι) :
    (correctionWord0 r).eval H R B (Fin.cons i v)=∑ a, ∑ b, ∑ p, ∑ q,
      H a b*H p q*R ![a,i,q,b]*B (Fin.cons p v) := by
  rw [Word2.eval_quad]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hL : (fun j : Fin 4 => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord0 r).wire (Sum.inl j)))=![a,i,q,b] := by
    funext j
    fin_cases j <;> rfl
  have hR : (fun j : Fin (r+1) => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord0 r).wire (Sum.inr j)))=Fin.cons p v := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  rw [hL,hR]
  ring

theorem eval_correctionWord1 (s : Fin r) (H : Matrix ι ι ℝ)
    (R : (Fin 4 → ι) → ℝ) (B : (Fin (r+1) → ι) → ℝ) (i : ι) (v : Fin r → ι) :
    (correctionWord1 s).eval H R B (Fin.cons i v)=∑ a, ∑ b, ∑ p, ∑ q,
      H a b*H p q*R ![i,a,v s,q]*B (Fin.cons b (Function.update v s p)) := by
  rw [Word2.eval_quad]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hL : (fun j : Fin 4 => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord1 s).wire (Sum.inl j)))=![i,a,v s,q] := by
    funext j
    fin_cases j <;> rfl
  have hR : (fun j : Fin (r+1) => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord1 s).wire (Sum.inr j)))=Fin.cons b (Function.update v s p) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · by_cases hjs : j=s
      · subst j
        simp [correctionWord1,correctionOneTo,pairAssignment]
      · simp [correctionWord1,correctionOneTo,hjs,Function.update_of_ne hjs]
  rw [hL,hR]
  ring

theorem eval_correctionWord2 (s : Fin r) (H : Matrix ι ι ℝ)
    (S : (Fin 5 → ι) → ℝ) (A : (Fin r → ι) → ℝ) (i : ι) (v : Fin r → ι) :
    (correctionWord2 s).eval H S A (Fin.cons i v)=∑ a, ∑ b, ∑ p, ∑ q,
      H a b*H p q*S ![i,a,v s,q,b]*A (Function.update v s p) := by
  rw [Word2.eval_quad]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hL : (fun j : Fin 5 => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord2 s).wire (Sum.inl j)))=![i,a,v s,q,b] := by
    funext j
    fin_cases j <;> rfl
  have hR : (fun j : Fin r => Sum.elim (Fin.cons i v) (pairAssignment a b p q)
      ((correctionWord2 s).wire (Sum.inr j)))=Function.update v s p := by
    funext j
    by_cases hjs : j=s
    · subst j
      simp [correctionWord2,correctionTwoTo,pairAssignment]
    · simp [correctionWord2,correctionTwoTo,hjs,Function.update_of_ne hjs]
  rw [hL,hR]
  ring

end Yau.LeafProofs.L23Aux
