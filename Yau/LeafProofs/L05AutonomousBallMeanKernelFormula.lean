import Yau.LeafProofs.L05AutonomousBallMeanKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_positive_rpow_intervalIntegrable {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (p : ℝ) :
    IntervalIntegrable (fun a : ℝ => a^p) volume s r := by
  have hCont : ContinuousOn (fun a : ℝ => a^p) (Ioi 0) :=
    continuousOn_id.rpow_const (fun _ ha => Or.inl (ne_of_gt ha))
  exact (hCont.mono (fun a ha => (lt_min hs hr).trans_le ha.1)).intervalIntegrable

theorem auto_green_integral_linear (d : ℕ) (r s : ℝ) :
    (∫ a in s..r, a/r^d)=(r^2-s^2)/(2*r^d) := by
  rw [intervalIntegral.integral_div,integral_id]
  ring

/-- The real-dimensional-two branch is the actual logarithmic Green kernel. -/
theorem auto_green_primitive_log (omega : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    autoGreenPrimitive 2 omega r s=
      (Real.log (r/s)-(r^2-s^2)/(2*r^2))/(2*omega) := by
  have hP := auto_positive_rpow_intervalIntegrable hs hr (1-(2 : ℝ))
  have hL : IntervalIntegrable (fun a : ℝ => a/r^2) volume s r := (continuous_id.intervalIntegrable s r).div_const _
  unfold autoGreenPrimitive autoGreenIntegrand
  simp only [Nat.cast_ofNat]
  rw [intervalIntegral.integral_sub hP hL,auto_green_integral_linear]
  have hLog : (∫ a in s..r, a^(1-(2 : ℝ)))=Real.log (r/s) := by
    rw [show 1-(2 : ℝ)=(-1 : ℝ) by norm_num]
    simp only [Real.rpow_neg_one]
    exact integral_inv_of_pos hs hr
  simpa only [Nat.cast_ofNat] using congrArg (fun z : ℝ =>
    (z-(r^2-s^2)/(2*r^2))/(2*omega)) hLog

/-- The higher-dimensional branch is a genuine negative power, with no missing case at d=2. -/
theorem auto_green_primitive_power {d : ℕ} (hd : 2 < d) (omega : ℝ) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    autoGreenPrimitive d omega r s=
      ((s^(2-(d : ℝ))-r^(2-(d : ℝ)))/((d : ℝ)-2)-
        (r^2-s^2)/(2*r^d))/((d : ℝ)*omega) := by
  have hP := auto_positive_rpow_intervalIntegrable hs hr (1-(d : ℝ))
  have hL : IntervalIntegrable (fun a : ℝ => a/r^d) volume s r := (continuous_id.intervalIntegrable s r).div_const _
  have hdR : (2 : ℝ) < d := by exact_mod_cast hd
  have hZero : (0 : ℝ)∉uIcc s r := fun h => (lt_min hs hr).not_ge h.1
  have hIntegral := integral_rpow (a := s) (b := r) (r := 1-(d : ℝ))
    (Or.inr ⟨by linarith,hZero⟩)
  rw [show 1-(d : ℝ)+1=2-(d : ℝ) by ring] at hIntegral
  unfold autoGreenPrimitive autoGreenIntegrand
  rw [intervalIntegral.integral_sub hP hL,auto_green_integral_linear,hIntegral]
  rw [show 2-(d : ℝ)=-((d : ℝ)-2) by ring,div_neg]
  ring

theorem auto_green_inner_derivative_flux {d : ℕ} (hd : 0 < d) (omega r : ℝ) :
    Tendsto (fun s : ℝ => s^(d-1)*(-autoGreenIntegrand d r s/((d : ℝ)*omega)))
      (𝓝[>] 0) (𝓝 (-1/((d : ℝ)*omega))) := by
  have hC : Continuous (fun s : ℝ => (s^d/r^d-1)/((d : ℝ)*omega)) := by fun_prop
  have hLim := (hC.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_pow hd.ne',zero_div,zero_sub] at hLim
  apply hLim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (auto_green_radial_flux hd omega r hs).symm

theorem auto_green_weighted_power {d : ℕ} (hd : 2 < d) (omega : ℝ) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    s^(d-1)*autoGreenPrimitive d omega r s=
      ((s-r^(2-(d : ℝ))*s^(d-1))/((d : ℝ)-2)-
        (r^2*s^(d-1)-s^(d+1))/(2*r^d))/((d : ℝ)*omega) := by
  have hCast : ((d-1 : ℕ) : ℝ)=(d : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
  have hMerge : s^(d-1)*s^(2-(d : ℝ))=s := by
    rw [← Real.rpow_natCast,← Real.rpow_add hs,hCast,show (d : ℝ)-1+(2-(d : ℝ))=1 by ring,Real.rpow_one]
  have hPow : s^(d-1)*s^2=s^(d+1) := by rw [← pow_add]; congr 1; omega
  rw [auto_green_primitive_power hd omega hr hs]
  calc
    _ = ((s^(d-1)*s^(2-(d : ℝ))-r^(2-(d : ℝ))*s^(d-1))/((d : ℝ)-2)-
        (r^2*s^(d-1)-s^(d-1)*s^2)/(2*r^d))/((d : ℝ)*omega) := by ring
    _ = _ := by rw [hMerge,hPow]

theorem auto_green_inner_value_flux_power {d : ℕ} (hd : 2 < d) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => s^(d-1)*autoGreenPrimitive d omega r s) (𝓝[>] 0) (𝓝 0) := by
  have hC : Continuous (fun s : ℝ =>
      ((s-r^(2-(d : ℝ))*s^(d-1))/((d : ℝ)-2)-
        (r^2*s^(d-1)-s^(d+1))/(2*r^d))/((d : ℝ)*omega)) := by fun_prop
  have hLim := (hC.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_pow (by omega : d-1 ≠ 0),zero_pow (by omega : d+1 ≠ 0),mul_zero,
    sub_zero,zero_div] at hLim
  apply hLim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (auto_green_weighted_power hd omega hr hs).symm

theorem auto_green_inner_value_flux_log (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => s^(2-1)*autoGreenPrimitive 2 omega r s) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hLog : Tendsto (fun s : ℝ => Real.log s*s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)
  have hPoly : Tendsto (fun s : ℝ => s*(r^2-s^2)/(2*r^2)) (𝓝[>] 0) (𝓝 0) := by
    have hC : Continuous (fun s : ℝ => s*(r^2-s^2)/(2*r^2)) := by fun_prop
    simpa only [zero_mul,zero_div] using (hC.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hLim := (((h0.mul_const (Real.log r)).sub hLog).sub hPoly).div_const (2*omega)
  simp only [zero_mul,sub_zero,zero_div] at hLim
  apply hLim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [auto_green_primitive_log omega hr hs,Real.log_div hr.ne' hs.ne']
  norm_num only [Nat.reduceSub,pow_one]
  ring

theorem auto_green_inner_value_flux {d : ℕ} (hd : 2 ≤ d) (omega : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => s^(d-1)*autoGreenPrimitive d omega r s) (𝓝[>] 0) (𝓝 0) := by
  rcases eq_or_lt_of_le hd with h|h
  · subst d
    exact auto_green_inner_value_flux_log omega hr
  · exact auto_green_inner_value_flux_power h omega hr

end Yau.LeafProofs.L05AutonomousAux
