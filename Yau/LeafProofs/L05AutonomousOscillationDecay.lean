import Yau.LeafProofs.L05AutonomousOscillationDecayIteration
import Yau.LeafProofs.L05AutonomousOscillationDecayGeometry

noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 2800000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual extrema contraction implies a full space-time pair estimate on the good set. -/
theorem auto_contraction_to_holder (n m : ℕ) (hm : 0 < m)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
      ∀ S : Set (Point n), S ⊆ autoOpen (0 : Space n) (5/8) 0 →
      ∀ B : ℝ, 0 ≤ B → ∀ w : Fin m → Point n → ℝ,
        (∀ j, ∀ p ∈ S, |w j p| ≤ B) →
        (∀ (c : Space n) (R T : ℝ), 0 < R → R ≤ 1/64 →
          autoClosed c R T ⊆ autoClosed (0 : Space n) (5/8) 0 →
          (S ∩ autoClosed c R T).Nonempty) →
        (∀ (c : Space n) (R T : ℝ), 0 < R → R ≤ 1/64 →
          autoClosed c R T ⊆ autoClosed (0 : Space n) (5/8) 0 →
          autoJetOsc S w c (R/8) T ≤ theta*autoJetOsc S w c R T) →
        ∀ j, ∀ p ∈ S ∩ autoClosed (0 : Space n) (9/16) 0,
          ∀ q ∈ S ∩ autoClosed (0 : Space n) (9/16) 0,
            |w j p-w j q| ≤ C*B*holderWeight eta p q := by
  obtain ⟨eta,he,he1,hslow⟩ := auto_jet_choose_exponent htheta1
  let R0 : ℝ := 1/64
  let V : ℝ := R0^eta
  let A : ℝ := (8 : ℝ)^eta
  let C : ℝ := 1+(2*(m : ℝ)*A+2)/V
  have hR0 : 0 < R0 := by norm_num [R0]
  have hV : 0 < V := Real.rpow_pos_of_pos hR0 eta
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) eta
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨eta,C,he,he1,hC,?_⟩
  intro S hS B hB w hb hNonempty hStep j p hp q hq
  let T := max p.2 q.2
  have hT : T < 0 := auto_jet_good_pair_top_neg hS hp.1 hq.1
  have hParent : autoClosed p.1 R0 T ⊆ autoClosed (0 : Space n) (5/8) 0 :=
    auto_jet_pair_parent_buffer hp.2 hq.2
  have hContain : ∀ r, 0 < r → r ≤ R0 →
      autoClosed p.1 r T ⊆ autoClosed (0 : Space n) (5/8) 0 :=
    fun r hr hr0 => (autoClosed_subset p.1 hr.le hr0 T).trans hParent
  have hne : ∀ r, 0 < r → r ≤ R0 → (S ∩ autoClosed p.1 r T).Nonempty :=
    fun r hr hr0 => hNonempty p.1 r T hr hr0 (hContain r hr hr0)
  have hstep : ∀ r, 0 < r → r ≤ R0 →
      autoJetOsc S w p.1 (r/8) T ≤ theta*autoJetOsc S w p.1 r T :=
    fun r hr hr0 => hStep p.1 r T hr hr0 (hContain r hr hr0)
  let D := parabolicDistance p q
  have hD : 0 ≤ D := auto_parabolic_distance_nonneg p q
  have hDpow : 0 ≤ D^eta := Real.rpow_nonneg hD eta
  have hWeight := auto_parabolic_distance_weight he.le he1.le p q
  have hAbs : |w j p-w j q| ≤ 2*B := by
    have hpv := abs_le.mp (hb j p hp.1)
    have hqv := abs_le.mp (hb j q hq.1)
    exact abs_le.mpr ⟨by linarith only [hpv.1,hqv.2], by linarith only [hpv.2,hqv.1]⟩
  have hMain : |w j p-w j q| ≤ C*B*D^eta := by
    by_cases hZero : D = 0
    · have hpq := auto_parabolic_distance_zero hZero
      rw [hpq, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hB) hDpow
    have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hZero)
    by_cases hNear : D ≤ R0
    · have hPair := auto_pair_in_distance_cylinder p q
      have hDecay := auto_jet_osc_decay w hb hB p.1 T hR0 htheta0.le he.le hslow.le
        hne hstep hDpos hNear
      have hBound := (auto_jet_osc_pair_le w hb p.1 D T j
        ⟨hp.1,hPair.1⟩ ⟨hq.1,hPair.2⟩).trans hDecay
      rw [Real.div_rpow hD hR0.le] at hBound
      change |w j p-w j q| ≤ A*(D^eta/V)*(2*(m : ℝ)*B) at hBound
      have hcoef : 2*(m : ℝ)*A ≤ C*V := by
        dsimp only [C]
        rw [add_mul, one_mul, div_mul_cancel₀ _ hV.ne']
        linarith only [hV.le]
      have hCoefBudget := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hB) hDpow
      have hScaled := mul_le_mul_of_nonneg_right hBound hV.le
      have heq : (A*(D^eta/V)*(2*(m : ℝ)*B))*V = 2*(m : ℝ)*A*B*D^eta := by
        field_simp [hV.ne']
      rw [heq] at hScaled
      apply (mul_le_mul_iff_of_pos_right hV).mp
      nlinarith only [hScaled,hCoefBudget]
    · have hFar : R0 ≤ D := (lt_of_not_ge hNear).le
      have hpw : V ≤ D^eta := Real.rpow_le_rpow hR0.le hFar he.le
      have hcoef : 2 ≤ C*V := by
        dsimp only [C]
        rw [add_mul, one_mul, div_mul_cancel₀ _ hV.ne']
        have hMA : 0 ≤ 2*(m : ℝ)*A := by positivity
        linarith only [hV.le,hMA]
      have hh := mul_le_mul_of_nonneg_left hpw (mul_nonneg hC.le hB)
      have htwo := mul_le_mul_of_nonneg_right hcoef hB
      nlinarith only [hAbs,hh,htwo]
  exact hMain.trans (mul_le_mul_of_nonneg_left hWeight (mul_nonneg hC.le hB))

end Yau.LeafProofs.L05AutonomousAux
