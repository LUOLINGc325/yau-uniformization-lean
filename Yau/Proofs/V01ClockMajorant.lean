import Yau.Proofs.V01PositiveMajorant
import Yau.Proofs.V01CostErrors

/-! Exact scalar assembly of the submean, replacement and physical-clock
inequalities. The physical test derivative may have either sign. -/

noncomputable section
open Matrix
open scoped Matrix
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

theorem fixed_majorant_from_clock_upper
    {H S : CotangentMatrix n} (hH : IsUnit H) (hS : IsUnit S)
    {r h₀ L I K B τ e e₁ e₂ e₃ : ℝ} (hr : 0 ≤ r) (hh₀ : 0 < h₀)
    (hSub : Real.exp L * (h₀ ^ 4)⁻¹ *
      bivectorCost (Hᴴ * H) (frameBivector S) ≤ I)
    (hReplacement : |K - I| ≤ e₁) (hClock : K ≤ B + e₂)
    (hBoundary : B ≤ τ + e + e₃) :
    symplecticP (fixedPositiveMajorant H S r h₀) ≤
      ((1 + r) ^ 2 * Real.exp (-L)) * (τ + (e + e₁ + e₂ + e₃)) := by
  have hScalar : 0 ≤ (1 + r) ^ 2 * Real.exp (-L) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hI : I ≤ τ + (e + e₁ + e₂ + e₃) := by
    have hAbs := (abs_le.mp hReplacement).1
    linarith
  have hCost : symplecticP (fixedPositiveMajorant H S r h₀) =
      ((1 + r) ^ 2 * Real.exp (-L)) *
        (Real.exp L * (h₀ ^ 4)⁻¹ * bivectorCost (Hᴴ * H) (frameBivector S)) := by
    rw [fixedPositiveMajorant_symplectic_cost hH hS hr hh₀, Real.exp_neg]
    field_simp [hh₀.ne', Real.exp_ne_zero L]
    <;> ring
  rw [hCost]
  exact mul_le_mul_of_nonneg_left (hSub.trans hI) hScalar

theorem fixed_majorant_from_clock_small_errors
    {H S : CotangentMatrix n} (hH : IsUnit H) (hS : IsUnit S)
    {r h₀ L I K B τ e e₁ e₂ e₃ β : ℝ} (hr : 0 ≤ r) (hh₀ : 0 < h₀)
    (hβ : 0 < β)
    (hSub : Real.exp L * (h₀ ^ 4)⁻¹ *
      bivectorCost (Hᴴ * H) (frameBivector S) ≤ I)
    (hReplacement : |K - I| ≤ e₁) (hClock : K ≤ B + e₂)
    (hBoundary : B ≤ τ + e + e₃)
    (hFactor : (1 + r) ^ 2 * Real.exp (-L) ≤ 2)
    (hFactorLoss : |(1 + r) ^ 2 * Real.exp (-L) - 1| * (1 + |τ|) ≤ β / 4)
    (hError : e + e₁ + e₂ + e₃ ≤ β / 4) :
    symplecticP (fixedPositiveMajorant H S r h₀) ≤ τ + β := by
  exact (fixed_majorant_from_clock_upper hH hS hr hh₀ hSub hReplacement hClock hBoundary).trans
    (scaled_cost_upper _ _ _ _ hβ
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hFactor hFactorLoss hError)

end Yau.Blueprint.V01Proof
