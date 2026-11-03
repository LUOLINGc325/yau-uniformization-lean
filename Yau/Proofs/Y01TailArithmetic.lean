import Yau.Proofs.Y07GridTail

/-! Exact restriction of the constructed frame and weight data to a later
regular canonical endpoint, without restarting its homological solution. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.NodeProofs.Y07Aux

variable {n : ℕ}

def shiftFrames (off : ℕ) (E : Frames n) : Frames n where
  start := fun k => E.start (off + k)
  finish := fun k => E.finish (off + k)

def shiftChanges (off : ℕ) (L : Changes n) : Changes n where
  plus := fun k => L.plus (off + k)
  minus := fun k => L.minus (off + k)

theorem rate_shift (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (off k : ℕ) (i : Fin n) :
    rate F (fun r => tk (off + r)) (shiftFrames off E) k i = rate F tk E (off + k) i := by
  simp only [rate, singularLength, transformedDerivative, shiftFrames, Nat.add_assoc]

theorem diagonal_shift (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (off k : ℕ) :
    diagonal F (fun r => tk (off + r)) (shiftFrames off E) k = diagonal F tk E (off + k) := by
  simp only [diagonal, singularLength, transformedDerivative, shiftFrames, Nat.add_assoc]

theorem jump_shift (E : Frames n) (off k : ℕ) :
    jump (shiftFrames off E) k = jump E (off + k) := by
  simp only [jump, shiftFrames, Nat.add_assoc]

theorem alignedJump_shift (E : Frames n) (L : Changes n) (off k : ℕ) :
    alignedJump (shiftFrames off E) (shiftChanges off L) k = alignedJump E L (off + k) := by
  simp only [alignedJump, shiftChanges, jump_shift, Nat.add_assoc]

theorem primaryDerivative_shift (reg : ℕ → Prop) (E : Frames n) (L : Changes n)
    (off : ℕ) (hstart : reg off) (k : ℕ) :
    primaryDerivative (fun r => reg (off + r)) (shiftFrames off E) (shiftChanges off L) k =
      primaryDerivative reg E L (off + k) := by
  classical
  cases k with
  | zero => simp only [Nat.add_zero, primaryDerivative, hstart, ite_true, shiftChanges, shiftFrames]
  | succ k =>
    have hsub : off + (k + 1) - 1 = off + k := by omega
    have hpos : 0 < off + (k + 1) := by omega
    simp only [primaryDerivative, shiftChanges, shiftFrames, Nat.add_sub_cancel,
      Nat.add_assoc, hsub, Nat.succ_pos, hpos, true_and]

theorem propagatedWeight_shift (p off q : ℕ) (μ : ℕ → Fin n → ℝ)
    (lam eps θ : ℝ) (b : ℕ × Fin n) :
    propagatedWeight p (fun k => μ (q + k)) off lam eps θ b =
      propagatedWeight p μ (q + off) lam eps θ b := by
  classical
  have hraw : rawWeight (fun k => μ (q + k)) off lam θ =
      rawWeight μ (q + off) lam θ := by
    funext a
    simp only [rawWeight, Nat.add_assoc]
  have hpass : Passage (fun k => μ (q + k)) off eps θ = Passage μ (q + off) eps θ := by
    funext a b
    simp only [Passage, Nat.add_assoc]
  have hreach : Reach p (fun k => μ (q + k)) off eps θ = Reach p μ (q + off) eps θ := by
    funext a b
    unfold Reach
    rw [hpass]
  have hset : ((vertices p).filter (fun a => Reach p (fun k => μ (q + k)) off eps θ a b)) =
      (vertices p).filter (fun a => Reach p μ (q + off) eps θ a b) := by
    apply Finset.filter_congr
    intro a ha
    rw [hreach]
  simp only [propagatedWeight, hraw, hset]

theorem weight_tail (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ)
    {jBase j₀ : ℕ} (hb : jBase ≤ j₀) (hlayout : GridLayout Q N M hm j₀)
    (μ : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n) :
    weight Q N M hm scale K eps j₀
      (fun r => μ (offset Q N M hm jBase j₀ + r)) k i =
      weight Q N M hm scale K eps jBase μ (offset Q N M hm jBase j₀ + k) i := by
  have hj : j₀ ≤ macroAt Q N M hm j₀ k := (hlayout.2.2.2.1 k).1
  simp only [weight, macroAt_tail Q N M hm hb hlayout,
    slotAt_tail Q N M hm hb hlayout, propagatedWeight_shift,
    ← offset_add Q N M hm hb hj]

theorem normalizedRegularTransition_shift
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (tk : ℕ → ℝ)
    (A Ainv : ℕ → PolyMap n) (E : Frames n) (L : Changes n) (off k : ℕ) :
    normalizedRegularTransition F (fun r => tk (off + r))
      (fun r => A (off + r)) (fun r => Ainv (off + r))
      (shiftFrames off E) (shiftChanges off L) k =
        normalizedRegularTransition F tk A Ainv E L (off + k) := by
  funext z
  simp only [normalizedRegularTransition, shiftFrames, shiftChanges, Nat.add_assoc]

end Yau.Proofs.Y01Aux
