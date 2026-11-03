import Yau.LeafProofs.L05AutonomousBallMeanKernelFormula
import Yau.LeafProofs.L05AutonomousBallMoments
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

theorem auto_green_weighted_integrable_power {d : ℕ} (hd : 2 < d) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s^(d-1)*autoGreenPrimitive d omega r s) (Ioo 0 r) := by
  let P : ℝ → ℝ := fun s =>
    ((s-r^(2-(d : ℝ))*s^(d-1))/((d : ℝ)-2)-
      (r^2*s^(d-1)-s^(d+1))/(2*r^d))/((d : ℝ)*omega)
  have hC : Continuous P := by fun_prop
  have hInt : IntegrableOn P (Ioo 0 r) :=
    (hC.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  apply (integrableOn_congr_fun (fun s hs => auto_green_weighted_power hd omega hr hs.1) measurableSet_Ioo).mpr
  exact hInt

theorem auto_green_weighted_integrable_log (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s^(2-1)*autoGreenPrimitive 2 omega r s) (Ioo 0 r) := by
  let P : ℝ → ℝ := fun s =>
    (s*Real.log r-s*Real.log s-s*(r^2-s^2)/(2*r^2))/(2*omega)
  have hC : Continuous P := by
    exact (((continuous_id.mul_const _).sub Real.continuous_mul_log).sub
      ((continuous_id.mul (continuous_const.sub (continuous_id.pow 2))).div_const _)).div_const _
  have hInt : IntegrableOn P (Ioo 0 r) :=
    (hC.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  apply (integrableOn_congr_fun (fun s hs => ?_) measurableSet_Ioo).mpr hInt
  rw [auto_green_primitive_log omega hr hs.1,Real.log_div hr.ne' hs.1.ne']
  dsimp only [P]
  norm_num only [Nat.reduceSub,pow_one]
  ring

theorem auto_green_weighted_integrable {d : ℕ} (hd : 2 ≤ d) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s : ℝ => s^(d-1)*autoRadialGreen d omega r s) (Ioo 0 r) := by
  have hInt : IntegrableOn (fun s : ℝ => s^(d-1)*autoGreenPrimitive d omega r s) (Ioo 0 r) := by
    rcases eq_or_lt_of_le hd with h|h
    · subst d
      exact auto_green_weighted_integrable_log omega hr
    · exact auto_green_weighted_integrable_power h omega hr
  apply (integrableOn_congr_fun (fun s hs => ?_) measurableSet_Ioo).mpr hInt
  rw [autoRadialGreen,ite_eq_left (show 0 < s ∧ s < r from hs)]

theorem auto_ballMean_kernel_integrableOn {n : ℕ} (hn : 0 < n) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : Space n => autoRadialGreen (2*n) omega r ‖x‖) (ball 0 r) := by
  have hdim : 0 < Module.finrank ℝ (Space n) := by rw [complexVector_finrank_real]; omega
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp hdim
  apply (integrableOn_fun_norm_addHaar (volume : Measure (Space n))).mpr
  rw [complexVector_finrank_real]
  simpa only [smul_eq_mul] using auto_green_weighted_integrable (by omega : 2 ≤ 2*n) omega hr

theorem auto_ballMean_kernel_integrable {n : ℕ} (hn : 0 < n) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : Space n => autoRadialGreen (2*n) omega r ‖x‖) := by
  let K : Space n → ℝ := fun x => autoRadialGreen (2*n) omega r ‖x‖
  have hEq : (ball (0 : Space n) r).indicator K=K := by
    funext x
    by_cases hx : x∈ball (0 : Space n) r
    · exact indicator_of_mem hx K
    · rw [indicator_of_notMem hx]
      apply (auto_radialGreen_zero_outside (2*n) omega r ?_).symm
      intro h
      exact hx (by simpa only [mem_ball,dist_zero_right] using h.2)
  change Integrable K
  rw [← hEq]
  exact (integrable_indicator_iff measurableSet_ball).mpr (auto_ballMean_kernel_integrableOn hn omega hr)

end Yau.LeafProofs.L05AutonomousAux
