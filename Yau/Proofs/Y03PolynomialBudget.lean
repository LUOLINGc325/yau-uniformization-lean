import Yau.Blueprint.Alignment

/-! Absorb fixed one-step coefficients into one uniform polynomial budget. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem uniform_polynomial_budget (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ J : ℕ, ∀ j, J ≤ j → 1 ≤ j ∧
      (2 : ℝ) ≤ (1 + (j : ℝ)) ^ (n + 3) ∧
      (n + 1 : ℝ) * (A * j + 1) ^ (n + 1) ≤ (1 + (j : ℝ)) ^ (n + 3) ∧
      (n : ℝ) ^ 2 * A * j ≤ (1 + (j : ℝ)) ^ (n + 3) := by
  let K := (n + 1 : ℝ) * (A + 1) ^ (n + 1)
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 1 (max K ((n : ℝ) ^ 2 * A)))
  refine ⟨J, ?_⟩
  intro j hj
  have hjR : (J : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 1 < (j : ℝ) := (le_max_left _ _).trans_lt (hJ.trans_le hjR)
  have hK : K ≤ (j : ℝ) :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (hJ.trans_le hjR).le))
  have hNA : (n : ℝ) ^ 2 * A ≤ (j : ℝ) :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (hJ.trans_le hjR).le))
  have hb : 1 ≤ 1 + (j : ℝ) := by linarith
  have hbasepow : 1 + (j : ℝ) ≤ (1 + (j : ℝ)) ^ (n + 3) := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ n + 3 by omega)
  have hKsq : K ≤ (1 + (j : ℝ)) ^ 2 := by nlinarith
  have hlinear : A * (j : ℝ) + 1 ≤ (A + 1) * (1 + (j : ℝ)) := by nlinarith
  have hpoly : (n + 1 : ℝ) * (A * j + 1) ^ (n + 1) ≤ (1 + (j : ℝ)) ^ (n + 3) := by
    calc
      _ ≤ (n + 1 : ℝ) * ((A + 1) * (1 + (j : ℝ))) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlinear _) (by positivity)
      _ = K * (1 + (j : ℝ)) ^ (n + 1) := by dsimp [K]; rw [mul_pow, mul_assoc]
      _ ≤ (1 + (j : ℝ)) ^ 2 * (1 + (j : ℝ)) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hKsq (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hquadratic : (n : ℝ) ^ 2 * A * j ≤ (1 + (j : ℝ)) ^ (n + 3) := by
    have hmul := mul_le_mul_of_nonneg_right hNA (by linarith : 0 ≤ (j : ℝ))
    have hp := pow_le_pow_right₀ hb (show 2 ≤ n + 3 by omega)
    nlinarith
  exact ⟨by exact_mod_cast h1.le, by linarith, hpoly, hquadratic⟩

end Yau.Blueprint.Alignment.Y03Proof
