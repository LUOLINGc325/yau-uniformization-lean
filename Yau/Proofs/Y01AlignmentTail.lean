import Yau.Proofs.Y01TailEstimates

/-! Exact restriction of the original aligned matrices, including the
absolute propagated weights and the regular start at a macro endpoint. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.NodeProofs.Y07Aux

variable {n : ℕ}

theorem changeAt_canonical_tail
    {Q : ℕ → ℝ} {N jBase j₀ : ℕ} {M hm scale K eps C c : ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {E : Frames n} {L : Changes n} {k : ℕ}
    (hChange : ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps jBase (rate F tk E))
      (macroAt Q N M hm jBase) (macroClock hm) C c L (offset Q N M hm jBase j₀ + k)) :
    ChangeAt (diagonal F (fun r => tk (offset Q N M hm jBase j₀ + r))
        (shiftFrames (offset Q N M hm jBase j₀) E))
      (weight Q N M hm scale K eps j₀
        (rate F (fun r => tk (offset Q N M hm jBase j₀ + r)) (shiftFrames (offset Q N M hm jBase j₀) E)))
      (macroAt Q N M hm j₀) (macroClock hm) C c (shiftChanges (offset Q N M hm jBase j₀) L) k := by
  let off := offset Q N M hm jBase j₀
  change ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps jBase (rate F tk E))
    (macroAt Q N M hm jBase) (macroClock hm) C c L (off + k) at hChange
  change ChangeAt (diagonal F (fun r => tk (off + r)) (shiftFrames off E))
    (weight Q N M hm scale K eps j₀ (rate F (fun r => tk (off + r)) (shiftFrames off E)))
    (macroAt Q N M hm j₀) (macroClock hm) C c (shiftChanges off L) k
  have hmu : rate F (fun r => tk (off + r)) (shiftFrames off E) =
      (fun r => rate F tk E (off + r)) := by
    funext r i
    exact rate_shift F tk E off r i
  have hmacro r : macroAt Q N M hm j₀ r = macroAt Q N M hm jBase (off + r) :=
    (macroAt_tail Q N M hm hb hgrid r).symm
  have hw r i : weight Q N M hm scale K eps j₀ (fun a => rate F tk E (off + a)) r i =
      weight Q N M hm scale K eps jBase (rate F tk E) (off + r) i :=
    weight_tail Q N M hm scale K eps hb hgrid (rate F tk E) r i
  simpa only [ChangeAt, shiftChanges, diagonal_shift, hmu, hw, hmacro, Nat.add_assoc] using hChange

theorem jumpAt_canonical_tail
    {Q : ℕ → ℝ} {N jBase j₀ : ℕ} {M hm scale K eps : ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Q N M hm j₀)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {E : Frames n} {L : Changes n} {k : ℕ}
    (hJump : JumpAt E (weight Q N M hm scale K eps jBase (rate F tk E)) L
      (offset Q N M hm jBase j₀ + k)) :
    JumpAt (shiftFrames (offset Q N M hm jBase j₀) E)
      (weight Q N M hm scale K eps j₀
        (rate F (fun r => tk (offset Q N M hm jBase j₀ + r)) (shiftFrames (offset Q N M hm jBase j₀) E)))
      (shiftChanges (offset Q N M hm jBase j₀) L) k := by
  let off := offset Q N M hm jBase j₀
  change JumpAt (shiftFrames off E)
    (weight Q N M hm scale K eps j₀ (rate F (fun r => tk (off + r)) (shiftFrames off E)))
    (shiftChanges off L) k
  have hmu : rate F (fun r => tk (off + r)) (shiftFrames off E) =
      (fun r => rate F tk E (off + r)) := by
    funext r i
    exact rate_shift F tk E off r i
  have hw r i : weight Q N M hm scale K eps j₀ (fun a => rate F tk E (off + a)) r i =
      weight Q N M hm scale K eps jBase (rate F tk E) (off + r) i :=
    weight_tail Q N M hm scale K eps hb hgrid (rate F tk E) r i
  intro i l hpass
  have hpass' : weight Q N M hm scale K eps jBase (rate F tk E) (off + k + 1) i <
      weight Q N M hm scale K eps jBase (rate F tk E) (off + k) l := by
    simpa only [hmu, hw, Nat.add_assoc] using hpass
  have hz := hJump i l hpass'
  simpa only [alignedJump_shift] using hz

theorem regular_start_at_offset
    {Q : ℕ → ℝ} {N jBase j₀ : ℕ} {M hm : ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Q N M hm j₀) (hreg : Regular Q N M j₀) :
    Regular Q N M (macroAt Q N M hm jBase (offset Q N M hm jBase j₀)) := by
  have hmacro := macroAt_tail Q N M hm hb hgrid 0
  rw [Nat.add_zero] at hmacro
  have hzero : macroAt Q N M hm j₀ 0 = j₀ := by
    simpa only [Yau.Blueprint.Alignment.Y03Proof.offset_self] using
      Yau.Blueprint.Alignment.Y03Proof.macroAt_offset Q N M hm (le_refl j₀)
  rw [hmacro, hzero]
  exact hreg

end Yau.Proofs.Y01Aux
