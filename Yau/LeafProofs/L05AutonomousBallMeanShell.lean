import Yau.LeafProofs.L05AutonomousBallMeanSource

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

def autoBallMeanShellWeight (n : ℕ) (a b s : ℝ) : ℝ :=
  (Icc a b).indicator (fun t : ℝ => (t^(2*n-1))⁻¹) s

theorem auto_ballMean_shell_weighted {n : ℕ} {a b : ℝ} {s : ℝ} (hs : 0 < s) :
    s^(2*n-1)*autoBallMeanShellWeight n a b s=(Icc a b).indicator (fun _ => (1 : ℝ)) s := by
  by_cases h : s∈Icc a b
  · simp only [autoBallMeanShellWeight,indicator_of_mem h,mul_inv_cancel₀ (pow_ne_zero _ hs.ne')]
  · simp only [autoBallMeanShellWeight,indicator_of_notMem h,mul_zero]

theorem auto_ballMean_shell_weight_integrable {n : ℕ} (hn : 0 < n) {a b : ℝ} :
    Integrable (fun x : Space n => autoBallMeanShellWeight n a b ‖x‖) := by
  have hdim : 0 < Module.finrank ℝ (Space n) := by rw [complexVector_finrank_real]; omega
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp hdim
  apply (integrable_fun_norm_addHaar (volume : Measure (Space n))).mpr
  rw [complexVector_finrank_real]
  have hInd : Integrable ((Icc a b).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (isCompact_Icc.measure_lt_top.ne))
  apply hInd.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simpa only [smul_eq_mul] using (auto_ballMean_shell_weighted (n := n) (a := a) (b := b) hs).symm

theorem auto_ballMean_shell_weight_integral {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : Space n, autoBallMeanShellWeight n a b ‖x‖)=
      (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*(b-a) := by
  have hdim : 0 < Module.finrank ℝ (Space n) := by rw [complexVector_finrank_real]; omega
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp hdim
  rw [integral_fun_norm_addHaar (volume : Measure (Space n)),complexVector_finrank_real]
  simp only [nsmul_eq_mul,smul_eq_mul]
  have hInt : (∫ s in Ioi (0 : ℝ), s^(2*n-1)*autoBallMeanShellWeight n a b s)=
      ∫ s in Ioi (0 : ℝ), (Icc a b).indicator (fun _ => (1 : ℝ)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact auto_ballMean_shell_weighted hs
  rw [hInt,setIntegral_indicator measurableSet_Icc]
  have hSet : Ioi (0 : ℝ) ∩ Icc a b=Icc a b := by
    exact inter_eq_right.mpr (fun s hs => ha.trans_le hs.1)
  rw [hSet,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul,mul_one]
  push_cast
  ring

theorem auto_ballMean_shell_integral_bound {n : ℕ} (hn : 0 < n) {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {g : Space n → ℝ}
    (hzero : ∀ x, ‖x‖ ∉ Icc a b → g x=0)
    (hbound : ∀ x, ‖x‖ ∈ Icc a b → ‖x‖^(2*n-1)*|g x| ≤ C) :
    |∫ x : Space n, g x| ≤ (2*n : ℝ)*(volume : Measure (Space n)).real (ball 0 1)*C*(b-a) := by
  have hDom (x : Space n) : ‖g x‖ ≤ C*autoBallMeanShellWeight n a b ‖x‖ := by
    by_cases hx : ‖x‖∈Icc a b
    · rw [autoBallMeanShellWeight,indicator_of_mem hx,Real.norm_eq_abs]
      have hp : 0 < ‖x‖^(2*n-1) := pow_pos (ha.trans_le hx.1) _
      rw [← div_eq_mul_inv,le_div_iff₀ hp]
      simpa only [mul_comm] using hbound x hx
    · simp only [hzero x hx,autoBallMeanShellWeight,indicator_of_notMem hx,mul_zero,norm_zero,le_refl]
  have h := norm_integral_le_of_norm_le ((auto_ballMean_shell_weight_integrable hn).const_mul C)
    (ae_of_all volume hDom)
  rw [integral_const_mul,auto_ballMean_shell_weight_integral hn ha hab,Real.norm_eq_abs] at h
  convert h using 1; ring

end Yau.LeafProofs.L05AutonomousAux
