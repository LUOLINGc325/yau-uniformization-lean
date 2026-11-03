import Yau.Proofs.C02JetProductBounds

/-! An explicit triangular inverse-jet recursion. Its order m+1 row uses
only inverse rows through m and the given original rows through m+1. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

def inverseJetMajorant (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  Nat.strongRecOn m fun m previous => if _hm : m = 0 then 2 else
    let v := fun i => if hi : i < m then previous i hi else 0
    binomialJetProduct (binomialJetProduct v (fun i => b (i + 1))) v (m - 1)

theorem inverseJetMajorant_unfold (b : ℕ → ℝ) (m : ℕ) :
    inverseJetMajorant b m = if _hm : m = 0 then 2 else
      let v := fun i => if _hi : i < m then inverseJetMajorant b i else 0
      binomialJetProduct (binomialJetProduct v (fun i => b (i + 1))) v (m - 1) := by
  rw [inverseJetMajorant, Nat.strongRecOn_eq]
  rfl

theorem inverseJetMajorant_zero (b : ℕ → ℝ) : inverseJetMajorant b 0 = 2 := by
  rw [inverseJetMajorant_unfold]
  simp

theorem inverseJetMajorant_succ (b : ℕ → ℝ) (m : ℕ) :
    inverseJetMajorant b (m + 1) =
      let v := fun i => if _hi : i < m + 1 then inverseJetMajorant b i else 0
      binomialJetProduct (binomialJetProduct v (fun i => b (i + 1))) v m := by
  rw [inverseJetMajorant_unfold]
  simp

theorem inverseJetMajorant_nonnegative {b : ℕ → ℝ} (hb : ∀ i, 0 ≤ b i) :
    ∀ m, 0 ≤ inverseJetMajorant b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [inverseJetMajorant_unfold]
    split_ifs with hm
    · norm_num
    · let v := fun i => if _hi : i < m then inverseJetMajorant b i else 0
      have hv (i : ℕ) : 0 ≤ v i := by
        dsimp only [v]
        split_ifs with hi
        · exact ih i hi
        · exact le_rfl
      exact binomialJetProduct_nonneg (fun k => binomialJetProduct_nonneg hv (fun i => hb (i + 1)) k)
        hv (m - 1)

end Yau.Blueprint.C02Proof
