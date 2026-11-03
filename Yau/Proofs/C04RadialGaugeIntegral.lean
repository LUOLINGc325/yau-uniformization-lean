import Yau.Proofs.C04RadialGaugeIntegralTimes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine radial-gauge connection and coframe integral formulas. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem radialGauge_smul_mem_ball {R : ℝ} {v : E} (hv : v ∈ Metric.ball (0 : E) R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball (0 : E) R := by
  have hvn : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt hvn

theorem radial_connection_integral (conn : E → E →L[ℝ] E →L[ℝ] E)
    (hc : ContDiff ℝ ∞ conn) {R : ℝ} (hR : 0 < R)
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, conn x x = 0)
    (v : E) (hv : v ∈ Metric.ball (0 : E) R) (w : E) :
    conn v w = ∫ t in (0 : ℝ)..1, t • radialGaugeCurvature conn (t • v) v w := by
  have hconnc := hc.continuous
  have hdconnc := hc.continuous_fderiv (by simp)
  have hprim : Continuous (fun t : ℝ => t • conn (t • v) w) := by fun_prop
  have hint : Continuous (fun t : ℝ => t • radialGaugeCurvature conn (t • v) v w) := by
    unfold radialGaugeCurvature
    fun_prop
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • conn (s • v) w)
      (t • radialGaugeCurvature conn (t • v) v w) t := by
    intro t ht
    exact radial_connection_time_derivative conn hc hrel v w ht.1
      (radialGauge_smul_mem_ball hv ⟨ht.1.le, ht.2.le⟩)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hprim.continuousOn hder (hint.intervalIntegrable 0 1)
  simpa only [one_smul, zero_smul, sub_zero] using hh.symm

theorem radial_coframe_integral (conn : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (hc : ContDiff ℝ ∞ conn) (hA : ContDiff ℝ ∞ A)
    {R : ℝ} (hR : 0 < R)
    (hconn : ∀ x ∈ Metric.ball (0 : E) R, conn x x = 0)
    (hrel : ∀ x ∈ Metric.ball (0 : E) R, A x x = x)
    (htorsion : ∀ x ∈ Metric.ball (0 : E) R, ∀ u w,
      (fderiv ℝ A x u) w - (fderiv ℝ A x w) u + conn x u (A x w) - conn x w (A x u) = 0)
    (v : E) (hv : v ∈ Metric.ball (0 : E) R) (w : E) :
    A v w = w + ∫ t in (0 : ℝ)..1, t • conn (t • v) w v := by
  have hconnc := hc.continuous
  have hAc := hA.continuous
  have hprim : Continuous (fun t : ℝ => t • A (t • v) w - t • w) := by fun_prop
  have hint : Continuous (fun t : ℝ => t • conn (t • v) w v) := by fun_prop
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s • A (s • v) w - s • w) (t • conn (t • v) w v) t := by
    intro t ht
    exact radial_coframe_time_derivative conn A hc hA hconn hrel htorsion v w ht.1
      (radialGauge_smul_mem_ball hv ⟨ht.1.le, ht.2.le⟩)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hprim.continuousOn hder (hint.intervalIntegrable 0 1)
  have heq : (∫ t in (0 : ℝ)..1, t • conn (t • v) w v) = A v w - w := by
    simpa only [one_smul, zero_smul, sub_zero, sub_self] using hh
  rw [heq]
  abel

end Yau.Proofs.C04Aux
