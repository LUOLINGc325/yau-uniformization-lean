import Yau.Proofs.C02RadialMajorantRecursion
import Yau.Proofs.C02RadialMajorantPositivity

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem radialJetMajorant_nonnegative {K : ℕ → ℝ} (hK : ∀ j, 0 ≤ K j) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ m, (radialJetMajorant K ρ m).Nonnegative := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · rw [radialJetMajorant_unfold, dif_pos hm]
      exact initialGaugeJetRow_nonnegative hK hρ
    · rw [radialJetMajorant_unfold, dif_neg hm]
      apply nextGaugeJetRow_nonnegative hK hρ
      intro i
      by_cases hi : i < m
      · simpa only [dif_pos hi] using ih i hi
      · simpa only [dif_neg hi] using zeroGaugeJetRow_nonnegative

end Yau.Blueprint.C02Proof
