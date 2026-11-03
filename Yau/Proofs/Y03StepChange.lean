import Yau.Proofs.Y03AlignmentStepScale
import Yau.Proofs.Y03ConjugationBound

/-! The constructed one-step matrix satisfies the exact ChangeAt, including its actual conjugate minus change. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem changeAt_of_step_matrix (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ) (j₀ : ℕ)
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ} {E : Frames n}
    (hE : SingularFrames F tk E) (k : ℕ) (P : Herm n) {A γ C c : ℝ}
    (heps : 0 ≤ eps) (hA : 0 ≤ A) (hc : c ≤ eps * γ / 2)
    (hdiag : ∀ i, P i i = 1)
    (hsupport : ∀ i l, i ≠ l → P i l ≠ 0 →
      weight Q N M hm scale K eps j₀ (rate F tk E) k i <
        weight Q N M hm scale K eps j₀ (rate F tk E) k l)
    (hnorm : matOpNorm P ≤ A * (macroAt Q N M hm j₀ k : ℝ))
    (hinverse : matOpNorm P + matOpNorm P⁻¹ ≤ (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C)
    (hbudget : (n : ℝ) ^ 2 * A * (macroAt Q N M hm j₀ k : ℝ) ≤
      (1 + (macroAt Q N M hm j₀ k : ℝ)) ^ C)
    (htime : γ * Real.sqrt (macroClock hm (macroAt Q N M hm j₀ k)) /
        (macroAt Q N M hm j₀ k : ℝ) ^ 2 ≤
      theta Q (macroAt Q N M hm j₀ k) * Real.log (tk (k + 1) / tk k)) :
    ChangeAt (diagonal F tk E) (weight Q N M hm scale K eps j₀ (rate F tk E))
      (macroAt Q N M hm j₀) (macroClock hm) C c
      (⟨fun _ => P, fun _ => (diagonal F tk E k)⁻¹ * P * diagonal F tk E k⟩ : Changes n) k := by
  let j := macroAt Q N M hm j₀ k
  let f := Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2
  have hf : 0 ≤ f := div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  have hD : IsUnit (diagonal F tk E k) := by
    rw [diagonal_eq_endpointDiagonal hE]
    exact endpointDiagonal_isUnit _ _
  have hP : IsUnit P := strict_weight_isUnit P
    (weight Q N M hm scale K eps j₀ (rate F tk E) k) hdiag hsupport
  have hexp : Real.exp (-(eps * theta Q j) * Real.log (tk (k + 1) / tk k) / 2) ≤
      Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) := by
    apply Real.exp_le_exp.2
    have h₁ := mul_le_mul_of_nonneg_right hc hf
    have htime' : γ * f ≤ theta Q j * Real.log (tk (k + 1) / tk k) := by
      simpa only [f, mul_div_assoc] using htime
    have h₂ : eps * γ / 2 * f ≤ eps * theta Q j * Real.log (tk (k + 1) / tk k) / 2 := by
      calc
        _ = eps * (γ * f) / 2 := by ring
        _ ≤ eps * (theta Q j * Real.log (tk (k + 1) / tk k)) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htime' heps) (by norm_num)
        _ = _ := by ring
    have hcf := h₁.trans h₂
    calc
      _ = -(eps * theta Q j * Real.log (tk (k + 1) / tk k) / 2) := by ring
      _ ≤ -(c * f) := neg_le_neg hcf
      _ = _ := by dsimp only [f]; ring

  have hsmall := actual_diagonal_change_small Q N M hm scale K eps j₀ hE k P hdiag hsupport
  have hminus : matOpNorm ((diagonal F tk E k)⁻¹ * P * diagonal F tk E k - 1) ≤
      (1 + (j : ℝ)) ^ C * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) := by
    apply hsmall.trans
    calc
      _ = ((n : ℝ) ^ 2 * matOpNorm P) * Real.exp
          (-(eps * theta Q j) * Real.log (tk (k + 1) / tk k) / 2) := by ring
      _ ≤ ((n : ℝ) ^ 2 * (A * j)) * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)) hexp (Real.exp_pos _).le (by positivity)
      _ = ((n : ℝ) ^ 2 * A * j) * Real.exp (-c * Real.sqrt (macroClock hm j) / (j : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le
  refine ⟨hdiag, hsupport, rfl, ?_, hinverse, hminus⟩
  exact diagonal_change_identity _ P hD hP

end Yau.Blueprint.Alignment.Y03Proof
