import Yau.Proofs.C02JetProductBounds

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem middleJetProduct_mono {a b A B : ℕ → ℝ} (m : ℕ)
    (ha : ∀ i ≤ m, a i ≤ A i) (hb : ∀ i ≤ m, b i ≤ B i)
    (ha0 : ∀ i, 0 ≤ a i) (hB0 : ∀ i, 0 ≤ B i) :
    middleJetProduct a b m ≤ middleJetProduct A B m := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i + 1 ≤ m := Nat.le_of_lt_succ (Nat.succ_lt_succ (Finset.mem_range.mp hi))
  have hj : (m + 1) - (i + 1) ≤ m := by omega
  have hh := (mul_le_mul_of_nonneg_left (hb _ hj) (ha0 (i + 1))).trans
    (mul_le_mul_of_nonneg_right (ha _ hi') (hB0 _))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg ((m + 1).choose (i + 1)))

theorem tripleJetProduct_top_bound {q b Q B : ℕ → ℝ} {K c : ℝ} (m : ℕ)
    (hq : ∀ i, 0 ≤ q i) (hb : ∀ i, 0 ≤ b i)
    (hQ : ∀ i, 0 ≤ Q i) (hB : ∀ i, 0 ≤ B i)
    (hqLower : ∀ i ≤ m, q i ≤ Q i) (hbLower : ∀ i ≤ m, b i ≤ B i)
    (hQ0 : Q 0 = K) (hB0 : B 0 = 3 / 2) (hqTop : q (m + 1) ≤ c) :
    binomialJetProduct (binomialJetProduct q b) b (m + 1) ≤
      3 * K * b (m + 1) + c * (3 / 2) ^ 2 +
        middleJetProduct Q B m * (3 / 2) + middleJetProduct (binomialJetProduct Q B) B m := by
  have hK : 0 ≤ K := hQ0 ▸ hQ 0
  have hc : 0 ≤ c := (hq _).trans hqTop
  have hq0 : q 0 ≤ K := (hqLower 0 (Nat.zero_le _)).trans_eq hQ0
  have hb0 : b 0 ≤ 3 / 2 := (hbLower 0 (Nat.zero_le _)).trans_eq hB0
  have hm := middleJetProduct_mono m hqLower hbLower hq hB
  have hInner (k : ℕ) (hk : k ≤ m) : binomialJetProduct q b k ≤ binomialJetProduct Q B k :=
    binomialJetProduct_mono k (fun i hi => hqLower i (hi.trans hk))
      (fun i hi => hbLower i (hi.trans hk)) (fun i hi => hq i) (fun i hi => hB i)
  have hOuter := middleJetProduct_mono m hInner hbLower
    (fun k => binomialJetProduct_nonneg hq hb k) hB
  rw [tripleJetProduct_succ_endpoints]
  apply add_le_add _ hOuter
  apply add_le_add _ (mul_le_mul hm hb0 (hb 0) (middleJetProduct_nonneg hQ hB m))
  apply add_le_add
  · calc
      2 * q 0 * b 0 * b (m + 1) ≤ 2 * K * (3 / 2) * b (m + 1) := by gcongr <;> exact hb _
      _ = 3 * K * b (m + 1) := by ring
  · exact mul_le_mul hqTop ((sq_le_sq₀ (hb 0) (by norm_num)).mpr hb0) (sq_nonneg _) hc

end Yau.Blueprint.C02Proof
