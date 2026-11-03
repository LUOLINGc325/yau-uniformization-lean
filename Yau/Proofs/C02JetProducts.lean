import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Binomial jet products and their two exact endpoint terms. The
remaining finite sum uses only strictly lower derivatives of its factors. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

def binomialJetProduct (a b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * a i * b (m - i)

def middleJetProduct (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, ((k + 1).choose (i + 1) : ℝ) * a (i + 1) * b ((k + 1) - (i + 1))

theorem binomialJetProduct_zero (a b : ℕ → ℝ) : binomialJetProduct a b 0 = a 0 * b 0 := by
  simp [binomialJetProduct]

theorem binomialJetProduct_nonneg {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (m : ℕ) :
    0 ≤ binomialJetProduct a b m := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha i)) (hb _)

theorem binomialJetProduct_succ_endpoints (a b : ℕ → ℝ) (k : ℕ) :
    binomialJetProduct a b (k + 1) =
      a 0 * b (k + 1) + a (k + 1) * b 0 + middleJetProduct a b k := by
  unfold binomialJetProduct
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.choose_self, Nat.sub_self]
  unfold middleJetProduct
  ring

theorem tripleJetProduct_succ_endpoints (q b : ℕ → ℝ) (k : ℕ) :
    binomialJetProduct (binomialJetProduct q b) b (k + 1) =
      2 * q 0 * b 0 * b (k + 1) + q (k + 1) * b 0 ^ 2 +
        middleJetProduct q b k * b 0 + middleJetProduct (binomialJetProduct q b) b k := by
  rw [binomialJetProduct_succ_endpoints, binomialJetProduct_zero,
    binomialJetProduct_succ_endpoints]
  ring

end Yau.Blueprint.C02Proof
