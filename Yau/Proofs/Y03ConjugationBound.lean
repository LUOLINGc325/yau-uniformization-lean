import Yau.Proofs.Y03Conjugation
import Yau.Proofs.Y03MatrixBound
import Yau.Proofs.Y03StepRicci
import Yau.Proofs.Y03Compactness

/-! Strict support converts the actual singular diagonal into uniform exponential decay. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem endpointDiagonal_conjugate_small (μ : Fin n → ℝ) (T : ℝ) (L : Herm n)
    (g B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B) (hdiag : ∀ i, L i i = 1)
    (hentry : ∀ i l, ‖L i l‖ ≤ B)
    (hgap : ∀ i l, i ≠ l → L i l ≠ 0 → g ≤ μ l - μ i) :
    matOpNorm ((endpointDiagonal μ T)⁻¹ * L * endpointDiagonal μ T - 1) ≤
      (n : ℝ) ^ 2 * (B * Real.exp (-g * T / 2)) := by
  apply matOpNorm_le_card_sq_mul (mul_nonneg hB (Real.exp_pos _).le)
  intro i l
  rw [Matrix.sub_apply, endpointDiagonal_conjugate_entry]
  by_cases hil : i = l
  · subst l
    simp only [sub_self, neg_zero, zero_mul, zero_div, Real.exp_zero, Complex.ofReal_one,
      mul_one, hdiag, Matrix.one_apply_eq, norm_zero]
    positivity
  · rw [Matrix.one_apply_ne hil, sub_zero]
    by_cases hzero : L i l = 0
    · rw [hzero, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-(μ l - μ i) * T / 2) ≤ Real.exp (-g * T / 2) := by
        apply Real.exp_le_exp.2
        have hmul := mul_le_mul_of_nonneg_right (hgap i l hil hzero) hT
        linarith
      exact mul_le_mul (hentry i l) he (Real.exp_pos _).le hB

theorem actual_diagonal_change_small (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ)
    (j₀ : ℕ) {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk : ℕ → ℝ} {E : Frames n} (hE : SingularFrames F tk E) (k : ℕ) (L : Herm n)
    (hdiag : ∀ i, L i i = 1)
    (hsupport : ∀ i l, i ≠ l → L i l ≠ 0 →
      weight Q N M hm scale K eps j₀ (rate F tk E) k i <
        weight Q N M hm scale K eps j₀ (rate F tk E) k l) :
    matOpNorm ((diagonal F tk E k)⁻¹ * L * diagonal F tk E k - 1) ≤
      (n : ℝ) ^ 2 * (matOpNorm L * Real.exp
        (-(eps * theta Q (macroAt Q N M hm j₀ k)) * Real.log (tk (k + 1) / tk k) / 2)) := by
  rw [diagonal_eq_endpointDiagonal hE]
  apply endpointDiagonal_conjugate_small _ _ _ _ _
    (log_time_ratio_pos (hE k).1 (hE k).2.1).le (norm_nonneg _) hdiag
  · exact fun i l => norm_entry_le_matOpNorm L i l
  · intro i l hil hL
    exact (strict_weight_support_rate_gap Q N M hm scale K eps j₀ (rate F tk E) k L hsupport i l hil hL).le

end Yau.Blueprint.Alignment.Y03Proof
