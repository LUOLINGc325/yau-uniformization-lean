import Yau.Proofs.C02JetProducts

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem binomialJetProduct_mono {a b A B : ℕ → ℝ} (m : ℕ)
    (ha : ∀ i ≤ m, a i ≤ A i) (hb : ∀ i ≤ m, b i ≤ B i)
    (ha0 : ∀ i ≤ m, 0 ≤ a i) (hB0 : ∀ i ≤ m, 0 ≤ B i) :
    binomialJetProduct a b m ≤ binomialJetProduct A B m := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hj : m - i ≤ m := Nat.sub_le _ _
  have hmul : a i * b (m - i) ≤ A i * B (m - i) :=
    (mul_le_mul_of_nonneg_left (hb _ hj) (ha0 i hi')).trans
      (mul_le_mul_of_nonneg_right (ha i hi') (hB0 _ hj))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg (m.choose i))

theorem middleJetProduct_nonneg {a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (k : ℕ) :
    0 ≤ middleJetProduct a b k := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ha _)) (hb _)

end Yau.Blueprint.C02Proof
