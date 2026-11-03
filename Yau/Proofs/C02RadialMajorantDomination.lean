import Yau.Proofs.C02RadialMajorantStep
import Yau.Proofs.C02RadialMajorantNonnegative

/-! Universal domination of all finite actual gauge jets. The scalar
witness is the explicit recursion, fixed before the actual jet data. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

theorem radialJetMajorant_dominates (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (J : ℕ → GaugeJetRow)
    (hJ : ∀ i, (J i).Nonnegative)
    (hInitial : (J 0).BoundedBy (initialGaugeJetRow K (radialGaugeRadius (K 0))))
    (hTensor : ∀ j m, (J (m + 1)).tensor j ≤
      binomialJetProduct (fun i => (J i).tensor (j + 1)) (fun i => (J i).differential) m +
        (4 + j) * binomialJetProduct (fun i => (J i).tensor j) (fun i => (J i).connection) m)
    (hCurvature : ∀ m, (J m).curvature ≤
      binomialJetProduct (binomialJetProduct (fun i => (J i).tensor 0) (fun i => (J i).differential))
        (fun i => (J i).differential) m)
    (hConnection : ∀ m, (J (m + 1)).connection ≤
      radialGaugeRadius (K 0) / ((m : ℝ) + 3) * (J (m + 1)).curvature +
        ((m : ℝ) + 1) / ((m : ℝ) + 2) * (J m).curvature)
    (hDifferential : ∀ m, (J (m + 1)).differential ≤
      radialGaugeRadius (K 0) / ((m : ℝ) + 3) * (J (m + 1)).connection +
        ((m : ℝ) + 1) / ((m : ℝ) + 2) * (J m).connection) :
    ∀ m, (J m).BoundedBy (radialJetMajorant K (radialGaugeRadius (K 0)) m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa only [radialJetMajorant_zero] using hInitial
    | succ m =>
      let previous := fun i => if _hi : i < m + 1 then
        radialJetMajorant K (radialGaugeRadius (K 0)) i else zeroGaugeJetRow
      have hp (i : ℕ) : (previous i).Nonnegative := by
        dsimp only [previous]
        split_ifs with hi
        · exact radialJetMajorant_nonnegative hK (radialGaugeRadius_pos (hK 0)).le i
        · exact zeroGaugeJetRow_nonnegative
      have hp0 : previous 0 = initialGaugeJetRow K (radialGaugeRadius (K 0)) := by
        dsimp only [previous]
        rw [dif_pos (Nat.zero_lt_succ m), radialJetMajorant_zero]
      have hprevious (i : ℕ) (hi : i ≤ m) : (J i).BoundedBy (previous i) := by
        dsimp only [previous]
        rw [dif_pos (Nat.lt_succ_of_le hi)]
        exact ih i (Nat.lt_succ_of_le hi)
      rw [radialJetMajorant_succ]
      exact radialMajorant_step K hK m J previous hJ hp hp0 hprevious
        (fun j => hTensor j m) (hCurvature (m + 1)) (hConnection m) (hDifferential m)

end Yau.Blueprint.C02Proof
