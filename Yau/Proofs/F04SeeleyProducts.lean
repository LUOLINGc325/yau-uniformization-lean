import Mathlib

/-! Finite product estimates for the explicit auxiliary time extension.
The bounds are uniform in the order of the finite Lagrange interpolation. -/

noncomputable section

namespace Yau.F04Proof.Seeley

def dyadic (k : ℕ) : ℝ := (2 : ℝ) ^ k

def denominatorProduct (M : ℕ) : ℝ :=
  ∏ j ∈ Finset.range M, (1 - (1 / 2 : ℝ) ^ (j + 1))

theorem denominatorProduct_succ (M : ℕ) :
    denominatorProduct (M + 1) = denominatorProduct M * (1 - (1 / 2 : ℝ) ^ (M + 1)) := by
  exact Finset.prod_range_succ _ _

theorem denominatorProduct_lower (M : ℕ) : (1 / 4 : ℝ) ≤ denominatorProduct M := by
  have hs : ∀ m : ℕ, 1 ≤ m →
      (1 / 4 : ℝ) + (1 / 2 : ℝ) ^ (m + 1) ≤ denominatorProduct m := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        norm_num [denominatorProduct]
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hq : (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 4 := by
        have he := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 2 ≤ m + 1 by omega)
        norm_num at he ⊢
        exact he
      have hq0 : 0 ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
      have hmul := mul_le_mul_of_nonneg_right (ih hm1)
        (show 0 ≤ 1 - (1 / 2 : ℝ) ^ (m + 1) by linarith)
      rw [denominatorProduct_succ]
      have hpow : (1 / 2 : ℝ) ^ (m + 1 + 1) = (1 / 2 : ℝ) ^ (m + 1) / 2 := by
        rw [pow_succ]
        ring
      rw [show m.succ + 1 = m + 1 + 1 by omega, hpow]
      nlinarith [mul_nonneg hq0 (show 0 ≤ 1 / 4 - (1 / 2 : ℝ) ^ (m + 1) by linarith)]
  by_cases hM : M = 0
  · subst M
    norm_num [denominatorProduct]
  · have hm := hs M (Nat.one_le_iff_ne_zero.mpr hM)
    have hp : 0 ≤ (1 / 2 : ℝ) ^ (M + 1) := by positivity
    linarith

theorem denominatorProduct_pos (M : ℕ) : 0 < denominatorProduct M :=
  lt_of_lt_of_le (by norm_num) (denominatorProduct_lower M)

def tailFactor (k l : ℕ) : ℝ :=
  (1 + dyadic (k + l + 1)) / (dyadic (k + l + 1) - dyadic k)

theorem dyadic_ge_one (k : ℕ) : 1 ≤ dyadic k := one_le_pow₀ (by norm_num)

theorem dyadic_pos (k : ℕ) : 0 < dyadic k := pow_pos (by norm_num) _

theorem dyadic_add (k l : ℕ) : dyadic (k + l) = dyadic k * dyadic l := pow_add _ _ _

theorem tailFactor_ge_one (k l : ℕ) : 1 ≤ tailFactor k l := by
  have hB := dyadic_ge_one k
  have hC : 2 ≤ dyadic (l + 1) := by
    simpa only [pow_one, dyadic] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ l + 1 by omega)
  have he : dyadic (k + l + 1) = dyadic k * dyadic (l + 1) := by
    rw [Nat.add_assoc, dyadic_add]
  have hden : 0 < dyadic (k + l + 1) - dyadic k := by rw [he]; nlinarith
  rw [tailFactor, le_div_iff₀ hden]
  linarith [dyadic_pos k]

def tailWeight (k r : ℕ) : ℝ := ∏ l ∈ Finset.range r, tailFactor k l

theorem tailWeight_ge_one (k r : ℕ) : 1 ≤ tailWeight k r :=
  Finset.one_le_prod₀ (fun l _ => tailFactor_ge_one k l)

theorem tailWeight_mono (k : ℕ) : Monotone (tailWeight k) := by
  apply monotone_nat_of_le_succ
  intro r
  rw [show tailWeight k (r + 1) = tailWeight k r * tailFactor k r from
    Finset.prod_range_succ _ _]
  nlinarith [tailWeight_ge_one k r, tailFactor_ge_one k r]

end Yau.F04Proof.Seeley
