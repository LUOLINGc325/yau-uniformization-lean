import Yau.Proofs.Y01TransitionBounds

/-! Conversion of the aligned changes' macro-index bounds into polynomial
bounds in the very same canonical clock. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Blueprint.Alignment.Y03Proof

 theorem constant_mul_real_power {A p s : ℝ} (hA : 0 ≤ A) (hs : 1 ≤ s) :
    A * (1 + s) ^ p ≤ (1 + s) ^ (A / Real.log 2 + p) := by
  rw [Real.rpow_add (by linarith : 0 < 1 + s)]
  exact mul_le_mul_of_nonneg_right (constant_le_real_power hA hs) (Real.rpow_nonneg (by linarith) _)

theorem polynomial_sum_bound {s p q x y : ℝ} (hs : 1 ≤ s)
    (hx : x ≤ (1 + s) ^ p) (hy : y ≤ (1 + s) ^ q) :
    x + y ≤ (1 + s) ^ (1 + max p q) := by
  have hbase : 1 ≤ 1 + s := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hbase (le_max_left p q)
  have hq := Real.rpow_le_rpow_of_exponent_le hbase (le_max_right p q)
  calc
    x + y ≤ 2 * (1 + s) ^ max p q := by linarith
    _ ≤ (1 + s) * (1 + s) ^ max p q :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 1 + s), Real.rpow_one]

theorem polynomial_product_bound {s p q x y : ℝ} (hs : 1 ≤ s)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ (1 + s) ^ p) (hy : y ≤ (1 + s) ^ q) :
    x * y ≤ (1 + s) ^ (p + q) := by
  rw [Real.rpow_add (by linarith : 0 < 1 + s)]
  exact mul_le_mul hx hy hy0 (Real.rpow_nonneg (by linarith) _)

theorem polynomial_nat_power_bound {s p x : ℝ} (hs : 1 ≤ s) (hx0 : 0 ≤ x)
    (hx : x ≤ (1 + s) ^ p) (m : ℕ) :
    x ^ m ≤ (1 + s) ^ (p * (m : ℝ)) := by
  calc
    _ ≤ ((1 + s) ^ p) ^ m := pow_le_pow_left₀ hx0 hx m
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 1 + s)]

theorem affine_real_power_bound {a : ℝ} (ha : 0 ≤ a) (p : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ ∀ s j : ℝ, 1 ≤ s → 0 ≤ j → j ≤ a * s →
      (1 + j) ^ p ≤ (1 + s) ^ q := by
  let A := (1 + a) ^ |p|
  have hA : 0 ≤ A := Real.rpow_nonneg (by linarith) _
  refine ⟨A / Real.log 2 + |p|, by positivity, ?_⟩
  intro s j hs hj hjbound
  have hbase : 1 + j ≤ (1 + a) * (1 + s) := by nlinarith
  have hpos : 0 < 1 + j := by linarith
  calc
    (1 + j) ^ p ≤ (1 + j) ^ |p| :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self p)
    _ ≤ ((1 + a) * (1 + s)) ^ |p| :=
      Real.rpow_le_rpow hpos.le hbase (abs_nonneg p)
    _ = A * (1 + s) ^ |p| := by
      rw [Real.mul_rpow (by linarith : 0 ≤ 1 + a) (by linarith : 0 ≤ 1 + s)]
    _ ≤ _ := constant_mul_real_power hA hs

theorem macroAt_le_clock_div {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}
    (hhm : 0 < hm) (k : ℕ) :
    (macroAt Q N M hm j₀ k : ℝ) ≤ gridClock Q N M hm j₀ k / hm := by
  have hlo := (gridClock_mem_Ico Q N M hm hhm j₀ k).1
  have hexp := Real.add_one_le_exp (hm * (macroAt Q N M hm j₀ k : ℝ))
  apply (le_div_iff₀ hhm).2
  unfold macroClock at hlo
  nlinarith

end Yau.Proofs.Y01Aux
