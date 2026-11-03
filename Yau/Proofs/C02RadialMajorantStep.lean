import Yau.Proofs.C02RadialMajorantPositivity
import Yau.Proofs.C02JetProductTopBound

/-! One simultaneous scalar induction step. The inputs are the genuine
finite-supremum inequalities established for the actual gauge fields. -/

noncomputable section
namespace Yau.Blueprint.C02Proof

def GaugeJetRow.BoundedBy (R S : GaugeJetRow) : Prop :=
  (∀ j, R.tensor j ≤ S.tensor j) ∧ R.differential ≤ S.differential ∧
    R.curvature ≤ S.curvature ∧ R.connection ≤ S.connection

theorem radialMajorant_step (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) (m : ℕ)
    (J previous : ℕ → GaugeJetRow)
    (hJ : ∀ i, (J i).Nonnegative) (hp : ∀ i, (previous i).Nonnegative)
    (hzero : previous 0 = initialGaugeJetRow K (radialGaugeRadius (K 0)))
    (hprevious : ∀ i ≤ m, (J i).BoundedBy (previous i))
    (hTensor : ∀ j, (J (m + 1)).tensor j ≤
      binomialJetProduct (fun i => (J i).tensor (j + 1)) (fun i => (J i).differential) m +
        (4 + j) * binomialJetProduct (fun i => (J i).tensor j) (fun i => (J i).connection) m)
    (hCurvature : (J (m + 1)).curvature ≤
      binomialJetProduct (binomialJetProduct (fun i => (J i).tensor 0) (fun i => (J i).differential))
        (fun i => (J i).differential) (m + 1))
    (hConnection : (J (m + 1)).connection ≤
      radialGaugeRadius (K 0) / ((m : ℝ) + 3) * (J (m + 1)).curvature +
        ((m : ℝ) + 1) / ((m : ℝ) + 2) * (J m).curvature)
    (hDifferential : (J (m + 1)).differential ≤
      radialGaugeRadius (K 0) / ((m : ℝ) + 3) * (J (m + 1)).connection +
        ((m : ℝ) + 1) / ((m : ℝ) + 2) * (J m).connection) :
    (J (m + 1)).BoundedBy (nextGaugeJetRow K (radialGaugeRadius (K 0)) m previous) := by
  let ρ := radialGaugeRadius (K 0)
  let b := fun i => (previous i).differential
  let a := fun i => (previous i).connection
  let q := fun j => binomialJetProduct (fun i => (previous i).tensor (j + 1)) b m +
    (4 + j) * binomialJetProduct (fun i => (previous i).tensor j) a m
  let L := q 0 * (3 / 2) ^ 2 + middleJetProduct (fun i => (previous i).tensor 0) b m * (3 / 2) +
    middleJetProduct (binomialJetProduct (fun i => (previous i).tensor 0) b) b m
  let c := ρ / ((m : ℝ) + 3)
  let d := ((m : ℝ) + 1) / ((m : ℝ) + 2)
  let bm := 2 * (c ^ 2 * L + c * d * (previous m).curvature + d * (previous m).connection)
  let fm := 3 * K 0 * bm + L
  have hc : 0 ≤ c := div_nonneg (radialGaugeRadius_pos (hK 0)).le (by positivity)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq (j : ℕ) : (J (m + 1)).tensor j ≤ q j := by
    apply (hTensor j).trans
    apply add_le_add
    · exact binomialJetProduct_mono m (fun i hi => (hprevious i hi).1 _)
        (fun i hi => (hprevious i hi).2.1) (fun i hi => (hJ i).1 _) (fun i hi => (hp i).2.1)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact binomialJetProduct_mono m (fun i hi => (hprevious i hi).1 _)
        (fun i hi => (hprevious i hi).2.2.2) (fun i hi => (hJ i).1 _) (fun i hi => (hp i).2.2.2)
  have hq0 : (previous 0).tensor 0 = K 0 := congrArg (fun R : GaugeJetRow => R.tensor 0) hzero
  have hb0 : b 0 = 3 / 2 := congrArg GaugeJetRow.differential hzero
  have hF : (J (m + 1)).curvature ≤ 3 * K 0 * (J (m + 1)).differential + L := by
    have ht := tripleJetProduct_top_bound m (fun i => (hJ i).1 0) (fun i => (hJ i).2.1)
      (fun i => (hp i).1 0) (fun i => (hp i).2.1) (fun i hi => (hprevious i hi).1 0)
      (fun i hi => (hprevious i hi).2.1) hq0 hb0 (hq 0)
    exact hCurvature.trans (ht.trans_eq (by dsimp [L]; ring))
  have hA : (J (m + 1)).connection ≤ c * (3 * K 0 * (J (m + 1)).differential + L) + d * (previous m).curvature :=
    hConnection.trans (add_le_add (mul_le_mul_of_nonneg_left hF hc)
      (mul_le_mul_of_nonneg_left (hprevious m le_rfl).2.2.1 hd))
  have hB : (J (m + 1)).differential ≤ c * (J (m + 1)).connection + d * (previous m).connection :=
    hDifferential.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hprevious m le_rfl).2.2.2 hd))
  have hTop : c ^ 2 * (3 * K 0) ≤ 1 / 2 := by
    calc
      _ = 3 * K 0 * radialGaugeRadius (K 0) ^ 2 / (((m + 1 : ℕ) : ℝ) + 2) ^ 2 := by
        have hden : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 3 := by push_cast; ring
        rw [hden]
        dsimp [c, ρ]
        rw [div_pow]
        ring
      _ ≤ 1 / 48 := radial_top_coefficient_le (hK 0) (m + 1) (by omega)
      _ ≤ 1 / 2 := by norm_num
  have hb : (J (m + 1)).differential ≤ bm := radial_two_inequality_absorption
    (J (m + 1)).connection (J (m + 1)).differential c d (3 * K 0) L
    (previous m).curvature (previous m).connection (hJ (m + 1)).2.1 hc hTop hA hB
  have hcoef : 0 ≤ (3 : ℝ) * K 0 := mul_nonneg (by norm_num) (hK 0)
  have hf : (J (m + 1)).curvature ≤ fm := hF.trans
    (add_le_add (mul_le_mul_of_nonneg_left hb hcoef) (le_refl L))
  have ha : (J (m + 1)).connection ≤ c * fm + d * (previous m).curvature :=
    hConnection.trans (add_le_add (mul_le_mul_of_nonneg_left hf hc)
      (mul_le_mul_of_nonneg_left (hprevious m le_rfl).2.2.1 hd))
  exact ⟨hq, hb, hf, ha⟩

end Yau.Blueprint.C02Proof
