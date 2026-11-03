import Yau.Proofs.Y05CoefficientSeries
import Yau.Proofs.Y05DecaySeries

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau MvPolynomial Yau.Proofs.Y02Aux
open scoped BigOperators

variable {n : ℕ}

/-- The coefficient tail in the frozen volume construction is an actual
absolutely convergent series with polynomial growth in the starting clock. -/
theorem exists_grid_coefficient_sums
    {s : ℕ → ℝ} {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ}
    {d : ℕ} {D σ Q L ch : ℝ}
    (hD : 0 ≤ D) (hσ : 0 < σ) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hch : 0 < ch)
    (hs : ∀ k, 0 < s k) (hsm : Monotone s)
    (hstepLo : ∀ k, ch * Real.sqrt (s k) ≤ s (k + 1) - s k)
    (hstepHi : ∀ k, s (k + 1) - s k ≤ Q * s k)
    (hdeg : ∀ k l, k ≤ l → (B k l).totalDegree ≤ d)
    (hzero : ∀ k l, k ≤ l → (B k l).coeff 0 = 0)
    (hbound : ∀ k l, k ≤ l → polynomialCoeffNorm (B k l) ≤
      L * (1 + (s (l + 1) - s l)) * min 1 (Real.exp (D * s k - σ * s l))) :
    ∃ (ell : ℕ → MvPolynomial (Fin n) ℂ) (H : ℝ), 0 < H ∧ ∀ k,
      (ell k).totalDegree ≤ d ∧ (ell k).coeff 0 = 0 ∧
      (∀ β, HasSum (fun r : ℕ => (B k (k + r)).coeff β) ((ell k).coeff β)) ∧
      polynomialCoeffNorm (ell k) ≤ H * (1 + s k) ^ 4 := by
  obtain ⟨a₀, ha₀, hlinear⟩ := grid_linear_lower_bound hch hs hstepLo
  let a := min 1 a₀
  have ha : 0 < a := lt_min zero_lt_one ha₀
  have halow : a ≤ a₀ := min_le_right _ _
  have haone : a ≤ 1 := min_le_left _ _
  have hlower (k r : ℕ) : a * ((r : ℝ) + 1) ≤ 1 + s (k + r) := by
    have H := hlinear (k + r)
    rw [Nat.cast_add] at H
    have Hr := mul_le_mul_of_nonneg_right halow (Nat.cast_nonneg (α := ℝ) r)
    have Hk : 0 ≤ a₀ * (k : ℝ) := mul_nonneg ha₀.le (Nat.cast_nonneg _)
    nlinarith [hs 0]
  obtain ⟨H, hH, hseries⟩ := weighted_decay_series_bound hD hσ hQ ha
  let kernel : ℕ → ℕ → ℝ := fun k r => (1 + (s (k + r + 1) - s (k + r))) *
    min 1 (Real.exp (D * s k - σ * s (k + r)))
  have hkernel (k : ℕ) : Summable (kernel k) ∧ ∑' r, kernel k r ≤ H * (1 + s k) ^ 4 :=
    hseries (s k) (hs k).le (fun r => s (k + r))
      (fun r => s (k + r + 1) - s (k + r))
      (fun r => (hs (k + r)).le)
      (fun r => sub_nonneg.mpr (hsm (Nat.le_succ (k + r))))
      (fun r => hstepHi (k + r)) (hlower k)
  let ell := fun k => coefficientSeriesPolynomial d (fun r => B k (k + r))
  let Htotal := 1 + ((scalarMonomials n d).card : ℝ) * L * H
  have hHt : 0 < Htotal := by dsimp [Htotal]; positivity
  refine ⟨ell, Htotal, hHt, ?_⟩
  intro k
  have hmaj : Summable (fun r => L * kernel k r) := (hkernel k).1.mul_left L
  have hBnorm (r : ℕ) : polynomialCoeffNorm (B k (k + r)) ≤ L * kernel k r := by
    have H := hbound k (k + r) (Nat.le_add_right k r)
    simpa only [kernel, mul_assoc] using H
  refine ⟨coefficientSeriesPolynomial_degree _ _,
    coefficientSeriesPolynomial_zero _ _ (fun r => hzero k (k + r) (Nat.le_add_right k r)),
    coefficientSeriesPolynomial_hasSum (fun r => hdeg k (k + r) (Nat.le_add_right k r))
      hmaj hBnorm, ?_⟩
  apply (coefficientSeriesPolynomial_norm_bound hmaj hBnorm).trans
  rw [tsum_mul_left]
  calc
    ((scalarMonomials n d).card : ℝ) * (L * ∑' r, kernel k r) ≤
        ((scalarMonomials n d).card : ℝ) * (L * (H * (1 + s k) ^ 4)) := by
      gcongr
      exact (hkernel k).2
    _ ≤ Htotal * (1 + s k) ^ 4 := by
      dsimp [Htotal]
      nlinarith [pow_nonneg (by linarith [hs k] : 0 ≤ 1 + s k) 4]

end Yau.Proofs.Y05Aux
