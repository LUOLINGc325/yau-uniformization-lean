import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section

namespace Yau.Proofs.Y05Aux

def HasPolynomialBound (s a : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ q : ℕ, ∀ k, a k ≤ K * (1 + s k) ^ q

theorem polynomialBound_mono {s a b : ℕ → ℝ}
    (ha : HasPolynomialBound s a) (hab : ∀ k, b k ≤ a k) : HasPolynomialBound s b := by
  obtain ⟨K, hK, q, hq⟩ := ha
  exact ⟨K, hK, q, fun k => (hab k).trans (hq k)⟩

theorem polynomialBound_const (s : ℕ → ℝ) (c : ℝ) :
    HasPolynomialBound s (fun _ => c) :=
  ⟨max 0 c, le_max_left _ _, 0, by intro k; simpa using le_max_right 0 c⟩

theorem polynomialBound_add {s a b : ℕ → ℝ} (hs : ∀ k, 0 ≤ s k)
    (ha : HasPolynomialBound s a) (hb : HasPolynomialBound s b) :
    HasPolynomialBound s (fun k => a k + b k) := by
  obtain ⟨A, hA, p, hp⟩ := ha
  obtain ⟨B, hB, q, hq⟩ := hb
  refine ⟨A + B, add_nonneg hA hB, p + q, ?_⟩
  intro k
  have hbase : 1 ≤ 1 + s k := by linarith [hs k]
  have ha' := (hp k).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hbase (Nat.le_add_right p q)) hA)
  have hb' := (hq k).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hbase (Nat.le_add_left q p)) hB)
  nlinarith

theorem polynomialBound_mul {s a b : ℕ → ℝ} (hs : ∀ k, 0 ≤ s k)
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : HasPolynomialBound s a) (hb : HasPolynomialBound s b) :
    HasPolynomialBound s (fun k => a k * b k) := by
  obtain ⟨A, hA, p, hp⟩ := ha
  obtain ⟨B, hB, q, hq⟩ := hb
  refine ⟨A * B, mul_nonneg hA hB, p + q, ?_⟩
  intro k
  have H := mul_le_mul (hp k) (hq k) (hb0 k)
    (mul_nonneg hA (pow_nonneg (by linarith [hs k]) p))
  exact H.trans_eq (by rw [pow_add]; ring)

theorem polynomialBound_pow {s a : ℕ → ℝ} (hs : ∀ k, 0 ≤ s k)
    (ha0 : ∀ k, 0 ≤ a k) (ha : HasPolynomialBound s a) (N : ℕ) :
    HasPolynomialBound s (fun k => a k ^ N) := by
  obtain ⟨A, hA, p, hp⟩ := ha
  refine ⟨A ^ N, pow_nonneg hA N, p * N, ?_⟩
  intro k
  exact (pow_le_pow_left₀ (ha0 k) (hp k) N).trans_eq (by rw [mul_pow, pow_mul])

/-- A positive first clock value absorbs the fixed multiplicative constant
into the single real exponent required by the original contract. -/
theorem polynomialBound_absorb {s a : ℕ → ℝ} (hs : ∀ k, 0 < s k) (hsm : Monotone s)
    (ha : HasPolynomialBound s a) : ∃ C : ℝ, 0 < C ∧ ∀ k, a k ≤ (1 + |s k|) ^ C := by
  obtain ⟨A, hA, q, hq⟩ := ha
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt A (by linarith [hs 0] : 1 < 1 + s 0)
  refine ⟨((N + q + 1 : ℕ) : ℝ), by positivity, ?_⟩
  intro k
  rw [abs_of_pos (hs k), Real.rpow_natCast]
  have hbase : 1 ≤ 1 + s k := by linarith [hs k]
  have hAbound : A ≤ (1 + s k) ^ N := hN.le.trans
    (pow_le_pow_left₀ (by linarith [hs 0]) (by linarith [hsm (Nat.zero_le k)]) N)
  calc
    a k ≤ A * (1 + s k) ^ q := hq k
    _ ≤ (1 + s k) ^ N * (1 + s k) ^ q :=
      mul_le_mul_of_nonneg_right hAbound (pow_nonneg (by linarith [hs k]) q)
    _ = (1 + s k) ^ (N + q) := (pow_add _ _ _).symm
    _ ≤ (1 + s k) ^ (N + q + 1) := pow_le_pow_right₀ hbase (Nat.le_succ _)

end Yau.Proofs.Y05Aux
