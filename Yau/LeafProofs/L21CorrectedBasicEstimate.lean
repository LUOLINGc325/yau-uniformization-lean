import Yau.LeafProofs.L21CoreEnergy
import Yau.LeafProofs.L21FiniteCoercivitySums

/-! The corrected basic weighted estimate on the actual compact core.
The d Dstar term has already been integrated by parts exactly. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

def coercivityYoung (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))

def coercivityRemainderConstant (n : ℕ) (M Z R : ℝ) : ℝ :=
  2 * (n : ℝ) ^ 2 * (M ^ 2 / (4 * coercivityYoung n)) +
    (n : ℝ) ^ 2 * (1 + Z ^ 2 / 4) + (n : ℝ) * (1 + R ^ 2 / 4)

theorem coercivityYoung_pos (n : ℕ) : 0 < coercivityYoung n := by unfold coercivityYoung; positivity

theorem coercivityYoung_absorb (n : ℕ) : 2 * (n : ℝ) * coercivityYoung n ≤ 1 / 2 := by
  unfold coercivityYoung
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

theorem coercivityRemainderConstant_nonneg (n : ℕ) (M Z R : ℝ) :
    0 ≤ coercivityRemainderConstant n M Z R := by
  unfold coercivityRemainderConstant
  have ht := coercivityYoung_pos n
  positivity

theorem corrected_basic_lower_bound (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (c d : Fin n → Fin n → Fin n → X n → ℂ)
    (hc : ∀ i j k, ContDiffOn ℝ ∞ (c i j k) O)
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O)
    (hbr : ∀ f : X n → ℂ, ContDiffOn ℝ ∞ f O → ∀ x ∈ O, ∀ i j,
      dbarA A i (conjugateD A j f) x - conjugateD A j (dbarA A i f) x =
        ∑ k, (c i j k x * dbarA A k f x + d i j k x * conjugateD A k f x))
    {M Z R : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hR : 0 ≤ R)
    (hcM : ∀ x ∈ O, ∀ i j k, ‖c i j k x‖ ≤ M)
    (hdM : ∀ x ∈ O, ∀ i j k, ‖d i j k x‖ ≤ M)
    (hdZ : ∀ x ∈ O, ∀ i j k, ‖dbarA A k (fun y => star (d i j k y)) x‖ ≤ Z)
    (hRem : ∀ x ∈ O, ∀ i j, ‖weightedCommutatorRemainder A d i j x‖ ≤ R)
    (v : Fin n → CompactTest O) :
    (1 / 2 : ℝ) * coreGradientEnergy hO hA φ v + coreLeviEnergy hO hA hφ hd v ≤
      compactFormQ hO hA hφ v + coercivityRemainderConstant n M Z R * coreScalarEnergy φ v := by
  let E (i : Fin n) : ℝ := weightedScalarEnergy φ (v i)
  let G (i j : Fin n) : ℝ := weightedScalarEnergy φ (testD hO hA i (v j))
  let t := coercivityYoung n
  let Y : ℝ := M ^ 2 / (4 * t)
  let bad (i j k : Fin n) : ℝ := t * G k j + Y * E i + t * G k i + Y * E j + E j + (Z ^ 2 / 4) * E i
  let badR (i j : Fin n) : ℝ := E j + (R ^ 2 / 4) * E i
  let P (i j : Fin n) : ℝ := testPair φ (v i)
    (testD hO hA i (testDs hO hA hφ j (v j)) - testDs hO hA hφ j (testD hO hA i (v j)))
  let L (i j : Fin n) : ℝ := testPair φ (v i)
    (multiplyLocalTest hO (contDiffOn_correctedLevi hO hA hφ hd i j) (v j))
  have hLine (i j : Fin n) : L i j - ((∑ k, bad i j k) + badR i j) ≤ P i j := by
    have hTerm (k : Fin n) : -(bad i j k) ≤
        testPair φ (v i) (multiplyLocalTest hO (hc i j k).neg (testD hO hA k (v j))) +
        testPair φ (v j) (multiplyLocalTest hO
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)) (testD hO hA k (v i))) +
        testPair φ (v i) (multiplyLocalTest hO
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA k
            ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)))) (v j)) := by
      have hpc : -(t * G k j + Y * E i) ≤
          testPair φ (v i) (multiplyLocalTest hO (hc i j k).neg (testD hO hA k (v j))) :=
        testPair_multiply_lower hO hφ (hc i j k).neg hM (coercivityYoung_pos n)
          (fun x hx => by simpa only [norm_neg] using hcM x hx i j k) _ _
      have hpd : -(t * G k i + Y * E j) ≤
          testPair φ (v j) (multiplyLocalTest hO
            ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)) (testD hO hA k (v i))) :=
        testPair_multiply_lower hO hφ
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)) hM (coercivityYoung_pos n)
          (fun x hx => by
            change ‖star (d i j k x)‖ ≤ M
            simpa only [norm_star] using hdM x hx i j k) _ _
      have hpz : -(E j + (Z ^ 2 / 4) * E i) ≤
          testPair φ (v i) (multiplyLocalTest hO
            ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA k
              ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)))) (v j)) := by
        simpa only [one_mul, mul_one] using testPair_multiply_lower hO hφ
          ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (contDiffOn_dbarA hO hA k
            ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hd i j k)))) hZ (t := 1) (by norm_num)
          (fun x hx => by
            change ‖star (dbarA A k (fun y => star (d i j k y)) x)‖ ≤ Z
            simpa only [norm_star] using hdZ x hx i j k) (v i) (v j)
      dsimp only [bad]
      linarith
    have hSum := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) => hTerm k
    simp only [Finset.sum_neg_distrib] at hSum
    have hRpair : -(badR i j) ≤ testPair φ (v i)
        (multiplyLocalTest hO (contDiffOn_weightedCommutatorRemainder hO hA hd i j) (v j)) := by
      simpa only [one_mul, mul_one] using testPair_multiply_lower hO hφ
        (contDiffOn_weightedCommutatorRemainder hO hA hd i j) hR (t := 1) (by norm_num)
        (fun x hx => hRem x hx i j) (v i) (v j)
    have hExpand := compact_commutator_pair_expansion hO hA hφ c d hc hd hbr i j (v i) (v j)
    change P i j = _ at hExpand
    linarith
  have hSum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hLine i j
  simp only [Finset.sum_sub_distrib] at hSum
  have hBad : (∑ i, ∑ j, ((∑ k, bad i j k) + badR i j)) =
      2 * (n : ℝ) * t * coreGradientEnergy hO hA φ v +
        coercivityRemainderConstant n M Z R * coreScalarEnergy φ v := by
    exact finite_coercivity_bad_sum n E G t Y (Z ^ 2 / 4) (R ^ 2 / 4)
  rw [hBad] at hSum
  change coreLeviEnergy hO hA hφ hd v - _ ≤ ∑ i, ∑ j, P i j at hSum
  have hBasic := weighted_basic_identity_core hO hA hφ v
  change compactFormQ hO hA hφ v = coreGradientEnergy hO hA φ v + (∑ i, ∑ j, P i j) at hBasic
  have hAbsorb := mul_le_mul_of_nonneg_right (coercivityYoung_absorb n) (coreGradientEnergy_nonneg hO hA φ v)
  linarith

end Yau.LeafProofs.L21Aux
