import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Exponential

noncomputable section

namespace Yau.Proofs.Y05Aux

open Filter
open scoped Topology BigOperators

theorem grid_linear_lower_bound {s : ℕ → ℝ} {ch : ℝ}
    (hch : 0 < ch) (hs : ∀ k, 0 < s k)
    (hstep : ∀ k, ch * Real.sqrt (s k) ≤ s (k + 1) - s k) :
    ∃ a : ℝ, 0 < a ∧ ∀ k, s 0 + a * k ≤ s k := by
  have hinc : StrictMono s := strictMono_nat_of_lt_succ fun k => by
    have hpos := mul_pos hch (Real.sqrt_pos.2 (hs k))
    have H := hstep k
    linarith
  let a := ch * Real.sqrt (s 0)
  have ha : 0 < a := mul_pos hch (Real.sqrt_pos.2 (hs 0))
  refine ⟨a, ha, ?_⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hroot := Real.sqrt_le_sqrt (hinc.monotone (Nat.zero_le k))
    have H : a ≤ s (k + 1) - s k :=
      (mul_le_mul_of_nonneg_left hroot hch.le).trans (hstep k)
    push_cast
    linarith

theorem fourth_power_exp_decay_bound {σ y : ℝ} (hσ : 0 < σ) (hy : 0 ≤ y) :
    (1 + y) ^ 4 * Real.exp (-σ * y / 2) ≤
      24 * Real.exp (σ / 2) / (σ / 2) ^ 4 := by
  have h := Real.pow_div_factorial_le_exp (x := (σ / 2) * (1 + y))
    (by positivity : 0 ≤ (σ / 2) * (1 + y)) 4
  norm_num only [Nat.factorial] at h
  have hp : (σ / 2) ^ 4 * (1 + y) ^ 4 ≤
      24 * Real.exp ((σ / 2) * (1 + y)) := by
    rw [mul_pow] at h
    linarith
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < σ / 2) 4)).mpr
  calc
    ((1 + y) ^ 4 * Real.exp (-σ * y / 2)) * (σ / 2) ^ 4 =
        ((σ / 2) ^ 4 * (1 + y) ^ 4) * Real.exp (-σ * y / 2) := by ring
    _ ≤ (24 * Real.exp ((σ / 2) * (1 + y))) * Real.exp (-σ * y / 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 24 * Real.exp (σ / 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

/-- A polynomial envelope keeps the near-clock range and the exponential
tail in one summable estimate. -/
theorem transition_decay_polynomial_envelope {C σ : ℝ} (hC : 0 ≤ C) (hσ : 0 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x, 0 ≤ x → ∀ y, 0 ≤ y →
      (1 + y) ^ 4 * min 1 (Real.exp (C * x - σ * y)) ≤ K * (1 + x) ^ 4 := by
  let D := 1 + 2 * C / σ
  let E := 24 * Real.exp (σ / 2) / (σ / 2) ^ 4
  let K := D ^ 4 + E + 1
  have hD : 1 ≤ D := by
    dsimp [D]
    have : 0 ≤ 2 * C / σ := by positivity
    linarith
  have hE : 0 < E := by dsimp [E]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro x hx y hy
  have hpowx : 1 ≤ (1 + x) ^ 4 := one_le_pow₀ (by linarith)
  by_cases hnear : σ * y ≤ 2 * C * x
  · have hy' : 1 + y ≤ D * (1 + x) := by
      dsimp [D]
      have h : y ≤ (2 * C * x) / σ := (le_div_iff₀ hσ).mpr (by nlinarith)
      have heq : (2 * C * x) / σ = (2 * C / σ) * x := by ring
      rw [heq] at h
      nlinarith [div_nonneg hC hσ.le]
    calc
      _ ≤ (1 + y) ^ 4 * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ ≤ (D * (1 + x)) ^ 4 := by
        simpa only [mul_one] using (pow_le_pow_left₀ (by linarith : 0 ≤ 1 + y) hy' 4)
      _ = D ^ 4 * (1 + x) ^ 4 := mul_pow _ _ _
      _ ≤ K * (1 + x) ^ 4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        linarith
  · have hexp : Real.exp (C * x - σ * y) ≤ Real.exp (-σ * y / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ (1 + y) ^ 4 * Real.exp (-σ * y / 2) :=
        mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hexp) (by positivity)
      _ ≤ E := fourth_power_exp_decay_bound hσ hy
      _ ≤ K * (1 + x) ^ 4 := by
        have hEK : E ≤ K := by dsimp [K]; nlinarith [pow_nonneg (by linarith : 0 ≤ D) 4]
        exact hEK.trans (le_mul_of_one_le_right hK.le hpowx)

end Yau.Proofs.Y05Aux
