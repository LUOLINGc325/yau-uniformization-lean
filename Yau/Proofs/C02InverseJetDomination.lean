import Yau.Proofs.C02InverseJetMajorants

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem inverseJetMajorant_dominates (a b : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (h0 : a 0 ≤ 2)
    (hStep : ∀ m, a (m + 1) ≤ binomialJetProduct
      (binomialJetProduct a (fun i => b (i + 1))) a m) :
    ∀ m, a m ≤ inverseJetMajorant b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa only [inverseJetMajorant_zero] using h0
    | succ m =>
      let v := fun i => if _hi : i < m + 1 then inverseJetMajorant b i else 0
      have hv (i : ℕ) : 0 ≤ v i := by
        dsimp only [v]
        split_ifs
        · exact inverseJetMajorant_nonnegative hb i
        · exact le_rfl
      have hp (i : ℕ) (hi : i ≤ m) : a i ≤ v i := by
        dsimp only [v]
        rw [dif_pos (Nat.lt_succ_of_le hi)]
        exact ih i (Nat.lt_succ_of_le hi)
      rw [inverseJetMajorant_succ]
      apply (hStep m).trans
      apply binomialJetProduct_mono m
      · intro k hk
        exact binomialJetProduct_mono k (fun i hi => hp i (hi.trans hk)) (fun i hi => le_refl _)
          (fun i hi => ha i) (fun i hi => hb (i + 1))
      · exact hp
      · intro k hk
        exact binomialJetProduct_nonneg ha (fun i => hb (i + 1)) k
      · intro i hi
        exact hv i

end Yau.Blueprint.C02Proof
