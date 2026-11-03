import Yau.Proofs.Y01TailArithmetic
import Yau.Proofs.Y03Grid

/-! The same frames, rates and propagated weights retain their original
estimates after exact restriction to a later regular macro endpoint. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.NodeProofs.Y07Aux

variable {n : ℕ}

theorem canonical_offset_beyond_threshold
    (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) {jBase j₀ kLate : ℕ}
    (hj : jBase + kLate ≤ j₀) : kLate ≤ offset Q N M hm jBase j₀ := by
  have h := Yau.Blueprint.Alignment.Y03Proof.sub_le_offset Q N M hm jBase j₀
  omega

theorem singularFrames_shift
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (off : ℕ) :
    SingularFrames F (fun k => tk (off + k)) (shiftFrames off E) := by
  intro k
  have hlength : singularLength F (fun r => tk (off + r)) (shiftFrames off E) k =
      singularLength F tk E (off + k) := by
    funext i
    simp only [singularLength, transformedDerivative, shiftFrames, Nat.add_assoc]
  obtain ⟨hpos, hstep, hstart, hfinish, htrans, hlengths, horder⟩ := hE (off + k)
  refine ⟨hpos, ?_, hstart, hfinish, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hstep
  · have ht : transformedDerivative F (fun r => tk (off + r)) (shiftFrames off E) k =
        transformedDerivative F tk E (off + k) := by
      simp only [transformedDerivative, shiftFrames, Nat.add_assoc]
    exact ht.trans (htrans.trans (diagonal_shift F tk E off k).symm)
  · rw [hlength]
    exact hlengths
  · rw [hlength]
    exact horder

theorem rateOrder_shift
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : RateOrder F tk E) (off : ℕ) :
    RateOrder F (fun k => tk (off + k)) (shiftFrames off E) := by
  refine ⟨?_, ?_⟩
  · intro k v
    simpa only [rate_shift, jump_shift, Nat.add_assoc] using hE.1 (off + k) v
  · intro i a b hab
    simpa only [rate_shift] using hE.2 i (Nat.add_le_add_left hab off)

theorem windowRateBounds_tail
    {Q : ℕ → ℝ} {N jBase j₀ : ℕ} {M hm b₀ : ℝ} {μ : ℕ → Fin n → ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Q N M hm j₀)
    (hμ : WindowRateBounds Q N M hm b₀ jBase μ) :
    WindowRateBounds Q N M hm b₀ j₀ (fun k => μ (offset Q N M hm jBase j₀ + k)) := by
  intro k i hk
  have hmacro := (macroAt_tail Q N M hm hb hgrid k).symm
  rw [hmacro] at hk ⊢
  exact hμ _ i hk

theorem weightEstimates_tail
    {Q : ℕ → ℝ} {N jBase j₀ : ℕ} {M hm scale K eps b : ℝ} {μ : ℕ → Fin n → ℝ}
    (hb : jBase ≤ j₀) (hgrid : GridLayout Q N M hm j₀)
    (hμ : WeightEstimates Q N M hm scale K eps b jBase μ) :
    WeightEstimates Q N M hm scale K eps b j₀
      (fun k => μ (offset Q N M hm jBase j₀ + k)) := by
  let off := offset Q N M hm jBase j₀
  change WeightEstimates Q N M hm scale K eps b j₀ (fun k => μ (off + k))
  have hmacro k : macroAt Q N M hm j₀ k = macroAt Q N M hm jBase (off + k) :=
    (macroAt_tail Q N M hm hb hgrid k).symm
  have hw k i : weight Q N M hm scale K eps j₀ (fun r => μ (off + r)) k i =
      weight Q N M hm scale K eps jBase μ (off + k) i :=
    weight_tail Q N M hm scale K eps hb hgrid μ k i
  refine ⟨?_, ?_, ?_, hμ.2.2.2⟩
  · intro k i hk
    rw [hmacro] at hk
    simpa only [hmacro, hw] using hμ.1 (off + k) i hk
  · intro k i l hk hk' hpass
    rw [hmacro] at hk hk'
    have hpass' : μ (off + k) l - eps * theta Q (macroAt Q N M hm jBase (off + k)) ≤
        μ (off + k + 1) i := by simpa only [hmacro, Nat.add_assoc] using hpass
    simpa only [hw, Nat.add_assoc] using hμ.2.1 (off + k) i l hk (by
      simpa only [Nat.add_assoc] using hk') hpass'
  · intro k i β hk hβ hforbidden
    rw [hmacro] at hk
    have hforbidden' : weight Q N M hm scale K eps jBase μ (off + k) i <
        ∑ l, (β l : ℝ) * weight Q N M hm scale K eps jBase μ (off + k) l := by
      simpa only [hw] using hforbidden
    simpa only [hmacro] using hμ.2.2.1 (off + k) i β hk hβ hforbidden'

end Yau.Proofs.Y01Aux
