import Yau.Proofs.Y03StepChange
import Yau.Proofs.Y03ChangeAssembly

/-! The native one-step construction extends the actual backward alignment, with later matrices unchanged. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem local_alignment_extension (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps b : ℝ) (j₀ : ℕ)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (horder : RateOrder F tk E)
    (hweights : WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E))
    (k : ℕ) (hreg : Regular Q N M (macroAt Q N M hm j₀ k))
    (hreg' : Regular Q N M (macroAt Q N M hm j₀ (k + 1)))
    {B γ C c : ℝ} (hB : 0 < B) (heps : 0 < eps) (hc : c ≤ eps * γ / 2)
    (hq : 0 < Q (macroAt Q N M hm j₀ k)) (hj : 1 ≤ macroAt Q N M hm j₀ k)
    (hμ : ∀ i, 0 ≤ rate F tk E k i ∧ rate F tk E k i ≤ B * Q (macroAt Q N M hm j₀ k))
    (hν : ∀ i, 0 ≤ rate F tk E (k + 1) i ∧ rate F tk E (k + 1) i ≤ B * Q (macroAt Q N M hm j₀ k))
    (hpoly : (n + 1 : ℝ) * (alignmentCoefficient n B eps * (macroAt Q N M hm j₀ k : ℝ) + 1) ^ (n + 1) ≤
      (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C)
    (hbudget : (n : ℝ) ^ 2 * alignmentCoefficient n B eps * (macroAt Q N M hm j₀ k : ℝ) ≤
      (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C)
    (htime : γ * Real.sqrt (macroClock hm (macroAt Q N M hm j₀ k)) /
        (macroAt Q N M hm j₀ k : ℝ) ^ 2 ≤
      theta Q (macroAt Q N M hm j₀ k) * Real.log (tk (k + 1) / tk k))
    (hboot : (1 + (macroAt Q N M hm j₀ (k + 1) : ℝ)) ^ C *
        Real.exp (-c * Real.sqrt (macroClock hm (macroAt Q N M hm j₀ (k + 1))) /
          (macroAt Q N M hm j₀ (k + 1) : ℝ) ^ 2) ≤ 1 / 2 ∧
      (1 + (macroAt Q N M hm j₀ (k + 1) : ℝ)) ^ C *
        Real.exp (-c * Real.sqrt (macroClock hm (macroAt Q N M hm j₀ (k + 1))) /
          (macroAt Q N M hm j₀ (k + 1) : ℝ) ^ 2) ≤
            eps / (64 * B * (macroAt Q N M hm j₀ k : ℝ) ^ 2))
    (next : Changes n)
    (hnext : ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
      (macroAt Q N M hm j₀) (macroClock hm) C c next (k + 1)) :
    ∃ L : Changes n,
      ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
        (macroAt Q N M hm j₀) (macroClock hm) C c L k ∧
      JumpAt E (weight Q N M hm scale K eps j₀ (rate F tk E)) L k ∧
      ∀ r, k + 1 ≤ r → L.plus r = next.plus r ∧ L.minus r = next.minus r := by
  let j := macroAt Q N M hm j₀ k
  let R := next.minus (k + 1) - 1
  let δ := matOpNorm R
  have hδ : 0 ≤ δ := norm_nonneg _
  have hδsmall : δ ≤ 1 / 2 ∧ δ ≤ eps / (64 * B * (j : ℝ) ^ 2) :=
    ⟨hnext.2.2.2.2.2.trans hboot.1, hnext.2.2.2.2.2.trans hboot.2⟩
  have hpass : ∀ i l, rate F tk E k l - eps * Q j / (j : ℝ) ^ 2 ≤ rate F tk E (k + 1) i →
      weight Q N M hm scale K eps j₀ (rate F tk E) k l ≤
        weight Q N M hm scale K eps j₀ (rate F tk E) (k + 1) i := by
    intro i l h
    apply hweights.2.1 k i l hreg hreg'
    simpa only [theta, mul_div_assoc] using h
  obtain ⟨P, hdiag, hsupport, _, hnorm, hinv, hzero⟩ := exists_linear_bound_alignment_matrix
    (rate F tk E k) (rate F tk E (k + 1))
    (weight Q N M hm scale K eps j₀ (rate F tk E) k)
    (weight Q N M hm scale K eps j₀ (rate F tk E) (k + 1)) (jump E k) R
    (jump_unitary hE k) hδ hδsmall.1 hq hB heps (by exact_mod_cast hj) le_rfl hμ hν
    (horder.1 k) hpass hδsmall.2
  have hchange := changeAt_of_step_matrix Q N M hm scale K eps j₀ hE k P heps.le
    (alignmentCoefficient_pos n B eps).le hc hdiag hsupport hnorm (hinv.trans hpoly) hbudget htime
  apply local_extension_from_matrix_change E (diagonal F tk E)
    (weight Q N M hm scale K eps j₀ (rate F tk E)) (macroAt Q N M hm j₀) (macroClock hm) C c
    next k P ((diagonal F tk E k)⁻¹ * P * diagonal F tk E k) hchange
  intro i l hil
  have hz := hzero i l hil
  have heq : (1 : Herm n) + R = next.minus (k + 1) := by dsimp [R]; abel
  rw [heq] at hz
  exact hz

end Yau.Blueprint.Alignment.Y03Proof
