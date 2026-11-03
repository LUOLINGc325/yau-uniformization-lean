import Mathlib.Analysis.Normed.Algebra.Logarithm
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

open Set Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachLogarithmAux

def logCoefficient (k : ℕ) : ℝ := (-1 : ℝ)^(k+1)/(k : ℝ)

@[simp] theorem logCoefficient_zero : logCoefficient 0=0 := by norm_num [logCoefficient]
@[simp] theorem logCoefficient_one : logCoefficient 1=1 := by norm_num [logCoefficient]

theorem logCoefficient_norm {k : ℕ} (_hk : 0 < k) : ‖logCoefficient k‖=1/(k : ℝ) := by
  simp only [logCoefficient,norm_div,norm_pow,norm_neg,norm_one,one_pow,Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]

theorem logCoefficient_norm_le_one (k : ℕ) : ‖logCoefficient k‖ ≤ 1 := by
  cases k with
  | zero => simp only [logCoefficient_zero,norm_zero]; norm_num
  | succ k =>
    rw [logCoefficient_norm (Nat.succ_pos k)]
    have hp : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
    exact (div_le_one hp).mpr (by exact_mod_cast (show 1 ≤ k+1 from by omega))

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

def logIncrement (z : A) : A := ∑' k : ℕ, logCoefficient k • z^k

theorem logIncrement_eq_series_sum : logIncrement A=(NormedSpace.logSeries ℝ A).sum := by
  funext z
  exact (NormedSpace.logSeries_sum_eq (𝕂 := ℝ) z).symm

theorem logSeries_norm_le_one (k : ℕ) : ‖NormedSpace.logSeries ℝ A k‖ ≤ 1 := by
  cases k with
  | zero =>
    have h := FormalMultilinearSeries.ofScalars_norm_eq_mul A logCoefficient 0
    rw [logCoefficient_zero,norm_zero,zero_mul] at h
    change ‖FormalMultilinearSeries.ofScalars A logCoefficient 0‖ ≤ 1
    rw [h]
    norm_num
  | succ k =>
    exact (FormalMultilinearSeries.ofScalars_norm_le A logCoefficient (k+1) (by omega)).trans
      (logCoefficient_norm_le_one (k+1))

theorem one_le_logSeries_radius : (1 : ℝ≥0∞) ≤ (NormedSpace.logSeries ℝ A).radius := by
  apply (NormedSpace.logSeries ℝ A).le_radius_of_bound (r := 1) 1
  intro k
  simpa only [NNReal.coe_one,one_pow,mul_one] using logSeries_norm_le_one A k

theorem norm_lt_one_mem_series_ball {z : A} (hz : ‖z‖ < 1) :
    z ∈ eball (0 : A) (NormedSpace.logSeries ℝ A).radius := by
  rw [mem_eball_zero_iff]
  have hOne : (‖z‖₊ : ℝ≥0∞) < 1 := by exact_mod_cast hz
  exact hOne.trans_le (one_le_logSeries_radius A)

variable [CompleteSpace A]

theorem logIncrement_summable {z : A} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => logCoefficient k • z^k) := by
  simpa only [NormedSpace.logSeries_apply_eq,logCoefficient] using
    (NormedSpace.logSeries ℝ A).summable (norm_lt_one_mem_series_ball A hz)

omit [CompleteSpace A] in
theorem logIncrement_summable_norm {z : A} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖logCoefficient k • z^k‖) := by
  simpa only [NormedSpace.logSeries_apply_eq,logCoefficient] using
    (NormedSpace.logSeries ℝ A).summable_norm_apply (norm_lt_one_mem_series_ball A hz)

theorem logIncrement_hasSum {z : A} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => logCoefficient k • z^k) (logIncrement A z) :=
  (logIncrement_summable A hz).hasSum

theorem logIncrement_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall (logIncrement A) (NormedSpace.logSeries ℝ A) 0 1 := by
  rw [logIncrement_eq_series_sum]
  exact ((NormedSpace.logSeries ℝ A).hasFPowerSeriesOnBall
    ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le (one_le_logSeries_radius A))).mono
    (by norm_num) (one_le_logSeries_radius A)

theorem logIncrement_analyticAt {z : A} (hz : ‖z‖ < 1) : AnalyticAt ℝ (logIncrement A) z := by
  apply (logIncrement_hasFPowerSeriesOnBall A).analyticAt_of_mem
  rw [mem_eball_zero_iff]
  have hn : ‖z‖₊ < (1 : ℝ≥0) := by exact_mod_cast hz
  simpa only [ENNReal.coe_one] using (enorm_lt_coe.mpr hn)

theorem logIncrement_contDiffOn : ContDiffOn ℝ ∞ (logIncrement A) (ball (0 : A) 1) := by
  intro z hz
  exact (logIncrement_analyticAt A (by simpa only [mem_ball,dist_zero_right] using hz)).contDiffAt.contDiffWithinAt

omit [CompleteSpace A] in
@[simp] theorem logIncrement_zero : logIncrement A 0=0 := by
  unfold logIncrement
  have hTerm (k : ℕ) : logCoefficient k • (0 : A)^k=0 := by cases k <;> simp
  simp only [hTerm,tsum_zero]

theorem logIncrement_hasFDerivAt_zero :
    HasFDerivAt (logIncrement A) (ContinuousLinearMap.id ℝ A) 0 := by
  have h := (logIncrement_hasFPowerSeriesOnBall A).hasFPowerSeriesAt.hasFDerivAt
  have hCoeff : continuousMultilinearCurryFin1 ℝ A A (NormedSpace.logSeries ℝ A 1)=ContinuousLinearMap.id ℝ A := by
    ext z
    change NormedSpace.logSeries ℝ A 1 (fun _ => z)=z
    rw [NormedSpace.logSeries_apply_eq]
    norm_num
  rwa [hCoeff] at h

end Yau.LeafProofs.L17BanachLogarithmAux
