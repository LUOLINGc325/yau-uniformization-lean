import Yau.Proofs.Y05GridEstimates

noncomputable section

namespace Yau.Proofs.Y05Aux

open scoped BigOperators Topology

theorem weighted_decay_pointwise_bound {C σ Q a K x y u : ℝ} {r : ℕ}
    (hQ : 0 ≤ Q) (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (hstep : u ≤ Q * y) (hlower : a * ((r : ℝ) + 1) ≤ 1 + y)
    (hK : 0 ≤ K)
    (henv : (1 + y) ^ 4 * min 1 (Real.exp (C * x - σ * y)) ≤ K * (1 + x) ^ 4) :
    (1 + u) * min 1 (Real.exp (C * x - σ * y)) ≤
      ((1 + Q) * K / a ^ 3) * (1 + x) ^ 4 / ((r : ℝ) + 1) ^ 3 := by
  let δ := min 1 (Real.exp (C * x - σ * y))
  have hδ : 0 ≤ δ := le_min (by norm_num) (Real.exp_pos _).le
  have ht : 0 ≤ (1 + u) * δ := mul_nonneg (by linarith) hδ
  have hstep' : 1 + u ≤ (1 + Q) * (1 + y) := by nlinarith
  have H : ((1 + u) * δ) * (1 + y) ^ 3 ≤ (1 + Q) * K * (1 + x) ^ 4 := by
    calc
      _ ≤ ((1 + Q) * (1 + y) * δ) * (1 + y) ^ 3 := by gcongr
      _ = (1 + Q) * ((1 + y) ^ 4 * δ) := by ring
      _ ≤ (1 + Q) * (K * (1 + x) ^ 4) := by gcongr
      _ = _ := by ring
  have hp : a ^ 3 * ((r : ℝ) + 1) ^ 3 ≤ (1 + y) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlower 3
  have H' := (mul_le_mul_of_nonneg_left hp ht).trans H
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < (r : ℝ) + 1) 3)).mpr
  rw [show ((1 + Q) * K / a ^ 3) * (1 + x) ^ 4 =
    ((1 + Q) * K * (1 + x) ^ 4) / a ^ 3 by ring]
  apply (le_div_iff₀ (pow_pos ha 3)).mpr
  convert H' using 1 <;> ring

/-- Linear separation of the grid turns the polynomial envelope into an
absolutely summable cubic series, uniformly in the starting clock. -/
theorem weighted_decay_series_bound {C σ Q a : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ) (hQ : 0 ≤ Q) (ha : 0 < a) :
    ∃ H : ℝ, 0 < H ∧ ∀ x, 0 ≤ x → ∀ y u : ℕ → ℝ,
      (∀ r, 0 ≤ y r) → (∀ r, 0 ≤ u r) →
      (∀ r, u r ≤ Q * y r) →
      (∀ r : ℕ, a * ((r : ℝ) + 1) ≤ 1 + y r) →
      Summable (fun r => (1 + u r) * min 1 (Real.exp (C * x - σ * y r))) ∧
      ∑' r, (1 + u r) * min 1 (Real.exp (C * x - σ * y r)) ≤ H * (1 + x) ^ 4 := by
  obtain ⟨K, hK, henv⟩ := transition_decay_polynomial_envelope hC hσ
  let U : ℕ → ℝ := fun r => 1 / ((r : ℝ) + 1) ^ 3
  have hU : Summable U := by
    have hs := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hU0 : 0 ≤ ∑' r, U r := tsum_nonneg (fun r => by dsimp [U]; positivity)
  let T := (1 + Q) * K / a ^ 3
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T * ((∑' r, U r) + 1), mul_pos hT (by linarith), ?_⟩
  intro x hx y u hy hu hstep hlower
  let b : ℕ → ℝ := fun r => (1 + u r) * min 1 (Real.exp (C * x - σ * y r))
  have hb0 (r : ℕ) : 0 ≤ b r := by
    exact mul_nonneg (by linarith [hu r]) (le_min (by norm_num) (Real.exp_pos _).le)
  have hbound (r : ℕ) : b r ≤ (T * (1 + x) ^ 4) * U r := by
    have H := weighted_decay_pointwise_bound hQ ha hx (hy r) (hu r) (hstep r)
      (hlower r) hK.le (henv x hx (y r) (hy r))
    simpa only [b, T, U, div_eq_mul_inv, one_mul, mul_assoc] using H
  have hmaj : Summable (fun r => (T * (1 + x) ^ 4) * U r) := hU.mul_left _
  have hb : Summable b := hmaj.of_nonneg_of_le hb0 hbound
  refine ⟨hb, ?_⟩
  have H := hb.tsum_le_tsum hbound hmaj
  rw [tsum_mul_left] at H
  apply H.trans
  have hx4 : 0 ≤ (1 + x) ^ 4 := by positivity
  nlinarith

end Yau.Proofs.Y05Aux
