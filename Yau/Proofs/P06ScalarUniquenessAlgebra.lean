import Mathlib

noncomputable section
open Filter
namespace Yau.NodeProofs.P06Aux

/-- Each application of the real cutoff energy inequality removes two
powers of the radius.  The initial polynomial bound is the only input. -/
theorem localizedEnergy_power_descent
    (E : ℕ → ℝ → ℝ) (d : ℕ) {c T : ℝ} (hc : 0 ≤ c) (hT : 0 < T)
    (hstep : ∀ j : ℕ, 1 ≤ j → ∀ A : ℝ, 0 ≤ A →
      (∀ t, 0 < t → t ≤ T → E (2 * j) t ≤ A) →
      ∀ t, 0 < t → t ≤ T → E j t ≤ 2 * T * (c / j) ^ 2 * A)
    (hbase : ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, 1 ≤ j →
      ∀ t, 0 < t → t ≤ T → E j t ≤ D * (j : ℝ) ^ d) :
    ∀ k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, 1 ≤ j →
      ∀ t, 0 < t → t ≤ T → E j t ≤ D * (j : ℝ) ^ d / (j : ℝ) ^ (2 * k) := by
  intro k
  induction k with
  | zero =>
      simpa only [Nat.mul_zero, pow_zero, div_one] using hbase
  | succ k ih =>
      obtain ⟨D, hD, hd⟩ := ih
      refine ⟨2 * T * c ^ 2 * (D * 2 ^ d), by positivity, ?_⟩
      intro j hj t ht htT
      have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
      let A : ℝ := D * 2 ^ d * (j : ℝ) ^ d / (j : ℝ) ^ (2 * k)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have houter : ∀ s, 0 < s → s ≤ T → E (2 * j) s ≤ A := by
        intro s hs hsT
        have hh := hd (2 * j) (by omega) s hs hsT
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hh
        calc
          E (2 * j) s ≤ D * (2 * (j : ℝ)) ^ d / (2 * (j : ℝ)) ^ (2 * k) := hh
          _ ≤ D * (2 * (j : ℝ)) ^ d / (j : ℝ) ^ (2 * k) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_left₀ hjpos.le (by linarith) _)
          _ = A := by dsimp [A]; rw [mul_pow]; ring
      have hh := hstep j hj A hA houter t ht htT
      convert hh using 1
      dsimp only [A]
      rw [div_pow, Nat.mul_succ, pow_add]
      field_simp
      <;> ring

end Yau.NodeProofs.P06Aux
