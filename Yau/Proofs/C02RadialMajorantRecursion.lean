import Yau.Proofs.C02RadialMajorants

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem radialJetMajorant_unfold (K : ℕ → ℝ) (ρ : ℝ) (m : ℕ) :
    radialJetMajorant K ρ m = if _hm : m = 0 then initialGaugeJetRow K ρ else
      nextGaugeJetRow K ρ (m - 1)
        (fun i => if _hi : i < m then radialJetMajorant K ρ i else zeroGaugeJetRow) := by
  rw [radialJetMajorant, Nat.strongRecOn_eq]
  rfl

theorem radialJetMajorant_zero (K : ℕ → ℝ) (ρ : ℝ) :
    radialJetMajorant K ρ 0 = initialGaugeJetRow K ρ := by
  rw [radialJetMajorant_unfold]
  simp

theorem radialJetMajorant_succ (K : ℕ → ℝ) (ρ : ℝ) (m : ℕ) :
    radialJetMajorant K ρ (m + 1) = nextGaugeJetRow K ρ m
      (fun i => if _hi : i < m + 1 then radialJetMajorant K ρ i else zeroGaugeJetRow) := by
  rw [radialJetMajorant_unfold]
  simp

end Yau.Blueprint.C02Proof
