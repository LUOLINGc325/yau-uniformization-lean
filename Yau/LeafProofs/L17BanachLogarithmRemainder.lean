import Yau.LeafProofs.L17BanachLogarithmPowerBounds
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachLogarithmAux

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def logRemainder (z : A) : A := logIncrement A z-z

@[simp] theorem logRemainder_zero : logRemainder A 0=0 := by simp [logRemainder]

theorem log_tail_summable {z : A} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => logCoefficient (k+2) • z^(k+2)) :=
  (summable_nat_add_iff 2).mpr (logIncrement_summable A hz)

theorem logRemainder_eq_tail {z : A} (hz : ‖z‖ < 1) :
    logRemainder A z=∑' k : ℕ, logCoefficient (k+2) • z^(k+2) := by
  have h := (logIncrement_summable A hz).sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,logCoefficient_zero,zero_smul,
    zero_add,logCoefficient_one,pow_one,one_smul] at h
  apply sub_eq_iff_eq_add.mpr
  simpa only [logIncrement,add_comm] using h.symm

theorem geometric_tail_hasSum {r D : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun k : ℕ => r^(k+1)*D) (r*(1-r)⁻¹*D) := by
  simpa only [pow_succ,mul_comm] using
    ((hasSum_geometric_of_lt_one hr hr1).mul_left r).mul_right D

theorem logRemainder_sub_norm_le {r : ℝ} (hr : 0 ≤ r) (hr4 : r ≤ 1/4)
    {z w : A} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖logRemainder A z-logRemainder A w‖ ≤ 8*r*‖z-w‖ := by
  have hr1 : r < 1 := by linarith
  have hz1 : ‖z‖ < 1 := hz.trans_lt hr1
  have hw1 : ‖w‖ < 1 := hw.trans_lt hr1
  rw [logRemainder_eq_tail A hz1,logRemainder_eq_tail A hw1,
    ← (log_tail_summable A hz1).tsum_sub (log_tail_summable A hw1)]
  calc
    ‖∑' k : ℕ, (logCoefficient (k+2) • z^(k+2)-logCoefficient (k+2) • w^(k+2))‖
        ≤ r*(1-r)⁻¹*‖z-w‖ := tsum_of_norm_bounded
      (geometric_tail_hasSum hr hr1) (log_tail_term_sub_norm_le hr hz hw)
    _ ≤ 8*r*‖z-w‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hd : 0 < 1-r := by linarith
      have hi : (1-r)⁻¹ ≤ 8 := by
        rw [inv_eq_one_div]
        apply (div_le_iff₀ hd).mpr
        linarith
      nlinarith

theorem logRemainder_norm_le {z : A} (hz : ‖z‖ ≤ 1/4) :
    ‖logRemainder A z‖ ≤ 8*‖z‖^2 := by
  have h := logRemainder_sub_norm_le A (norm_nonneg z) hz (le_refl ‖z‖)
    (show ‖(0 : A)‖ ≤ ‖z‖ by simp)
  simpa only [logRemainder_zero,sub_zero,pow_two,mul_assoc] using h

theorem logRemainder_contDiffOn :
    ContDiffOn ℝ ∞ (logRemainder A) (ball (0 : A) 1) :=
  (logIncrement_contDiffOn A).sub contDiffOn_id

theorem logRemainder_hasFDerivAt_zero :
    HasFDerivAt (logRemainder A) (0 : A →L[ℝ] A) 0 := by
  have h := (logIncrement_hasFDerivAt_zero A).sub (hasFDerivAt_id (𝕜 := ℝ) (0 : A))
  convert h using 1
  · funext z
    rfl
  · simp

@[simp] theorem logRemainder_fderiv_zero : fderiv ℝ (logRemainder A) 0=0 :=
  (logRemainder_hasFDerivAt_zero A).fderiv

theorem logRemainder_fderiv_norm_le {z : A} (hz : ‖z‖ ≤ 1/8) :
    ‖fderiv ℝ (logRemainder A) z‖ ≤ 16*‖z‖ := by
  by_cases hzero : z=0
  · simp [hzero]
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  have hn : ball (0 : A) (2*‖z‖) ∈ nhds z := isOpen_ball.mem_nhds (by
    simp only [mem_ball,dist_zero_right]
    linarith)
  filter_upwards [hn] with w hw
  have hw' : ‖w‖ ≤ 2*‖z‖ := (by simpa only [mem_ball,dist_zero_right] using hw : ‖w‖ < 2*‖z‖).le
  have h := logRemainder_sub_norm_le A (by positivity : 0 ≤ 2*‖z‖)
    (by linarith : 2*‖z‖ ≤ 1/4) hw' (by linarith : ‖z‖ ≤ 2*‖z‖)
  convert h using 1
  ring

end Yau.LeafProofs.L17BanachLogarithmAux
