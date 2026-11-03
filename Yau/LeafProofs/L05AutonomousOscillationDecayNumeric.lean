import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

noncomputable section
open Filter Set
open scoped Topology
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

/-- The actual contraction radii use the prescribed factor 1/8. -/
def autoJetRadius (R : ℝ) (j : ℕ) : ℝ := R*(1/8 : ℝ)^j

theorem autoJetRadius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < autoJetRadius R j := by
  dsimp only [autoJetRadius]
  positivity

theorem autoJetRadius_le {R : ℝ} (hR : 0 ≤ R) (j : ℕ) : autoJetRadius R j ≤ R := by
  simpa only [autoJetRadius, mul_one] using
    mul_le_mul_of_nonneg_left
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/8) (by norm_num) (n := j)) hR

theorem autoJetRadius_succ (R : ℝ) (j : ℕ) :
    autoJetRadius R (j+1) = autoJetRadius R j/8 := by
  dsimp only [autoJetRadius]
  rw [pow_succ]
  ring

/-- A genuine exponent slower than the literal 1/8 contraction, before every field. -/
theorem auto_jet_choose_exponent {theta : ℝ} (ht : theta < 1) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ theta < (1/8 : ℝ)^eta := by
  let eta := min (1/2) ((1-theta)/8)
  have he : 0 < eta := lt_min (by norm_num) (div_pos (sub_pos.mpr ht) (by norm_num))
  have he1 : eta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have het : eta ≤ (1-theta)/8 := min_le_right _ _
  have hlog : Real.log 8 < 8 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)).trans_lt (by norm_num)
  have hexp : (1/8 : ℝ)^eta = Real.exp (-eta*Real.log 8) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/8), one_div, Real.log_inv]
    congr 1
    ring
  have hlower : 1-eta*Real.log 8 ≤ (1/8 : ℝ)^eta := by
    rw [hexp]
    have hh := Real.add_one_le_exp (-eta*Real.log 8)
    linarith only [hh]
  have hmul := mul_lt_mul_of_pos_left hlog he
  exact ⟨eta,he,he1,(by nlinarith only [het,hmul] : theta < 1-eta*Real.log 8).trans_le hlower⟩

/-- Actual geometric interval selection, with no decay or modulus assumed. -/
theorem autoJetRadius_cover {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ j : ℕ, r ≤ autoJetRadius R j ∧ autoJetRadius R j < 8*r := by
  obtain ⟨j,hjLow,hjUp⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0 : ℝ) < 1/8) (by norm_num)
  refine ⟨j,?_,?_⟩
  · have hh := (div_le_iff₀ hR).mp hjUp
    simpa only [autoJetRadius, mul_comm] using hh
  · have hh := (lt_div_iff₀ hR).mp hjLow
    rw [pow_succ] at hh
    change R*(1/8 : ℝ)^j < 8*r
    nlinarith only [hh]

/-- The actual geometric interval bounds the contraction power by the chosen real power. -/
theorem auto_jet_power_bound {theta eta R r : ℝ} {j : ℕ}
    (ht : 0 ≤ theta) (he : 0 ≤ eta) (hslow : theta ≤ (1/8 : ℝ)^eta)
    (hR : 0 < R) (hr : 0 ≤ r) (hj : autoJetRadius R j < 8*r) :
    theta^j ≤ (8 : ℝ)^eta*(r/R)^eta := by
  have hnear : (1/8 : ℝ)^j ≤ 8*(r/R) := by
    have hh : (1/8 : ℝ)^j < (8*r)/R :=
      (lt_div_iff₀ hR).mpr (by simpa only [autoJetRadius, mul_comm] using hj)
    simpa only [mul_div_assoc] using hh.le
  calc
    _ ≤ ((1/8 : ℝ)^eta)^j := pow_le_pow_left₀ ht hslow j
    _ = ((1/8 : ℝ)^j)^eta := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1/8),
        mul_comm eta (j : ℝ), Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1/8)]
    _ ≤ (8*(r/R))^eta := Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hnear he
    _ = _ := Real.mul_rpow (by norm_num) (div_nonneg hr hR.le)

end Yau.LeafProofs.L05AutonomousAux
