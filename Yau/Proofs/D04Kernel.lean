import Yau.Proofs.D04BallMean

open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau

variable {n : ℕ}

def radialBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

def radialNumerator (t : ℝ) (v : ComplexVector n) : ℝ :=
  radialBump (‖v‖ ^ 2 / t ^ 2)

def radialMass (n : ℕ) (t : ℝ) : ℝ :=
  ∫ v : ComplexVector n, radialNumerator t v

def radialKernel (t : ℝ) (v : ComplexVector n) : ℝ :=
  radialNumerator t v / radialMass n t

theorem contDiff_radialNumerator (t : ℝ) : ContDiff ℝ ∞ (radialNumerator (n := n) t) :=
  radialBump.contDiff.comp ((contDiff_norm_sq ℝ).div_const _)

theorem radialNumerator_nonneg (t : ℝ) (v : ComplexVector n) : 0 ≤ radialNumerator t v :=
  radialBump.nonneg

theorem radialNumerator_zero (t : ℝ) : radialNumerator t (0 : ComplexVector n) = 1 := by
  unfold radialNumerator
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
  exact radialBump.one_of_mem_closedBall (Metric.mem_closedBall_self radialBump.rIn_pos.le)

theorem radialNumerator_zero_outer {t : ℝ} (ht : 0 < t) {v : ComplexVector n}
    (hv : t ≤ ‖v‖) : radialNumerator t v = 0 := by
  apply radialBump.zero_of_le_dist
  change (1 : ℝ) ≤ |‖v‖ ^ 2 / t ^ 2 - 0|
  rw [sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  nlinarith [norm_nonneg v]

theorem radialNumerator_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (radialNumerator (n := n) t) ⊆ Metric.closedBall 0 t := by
  apply Metric.isClosed_closedBall.closure_subset_iff.mpr
  intro v hv
  by_contra h
  have hnorm : t ≤ ‖v‖ := by
    have h' : ¬ ‖v‖ ≤ t := by simpa only [Metric.mem_closedBall, dist_zero_right] using h
    exact (not_le.mp h').le
  exact hv (radialNumerator_zero_outer ht hnorm)

theorem radialNumerator_hasCompactSupport {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (radialNumerator (n := n) t) :=
  (isCompact_closedBall (0 : ComplexVector n) t).of_isClosed_subset (isClosed_tsupport _)
    (radialNumerator_tsupport_subset ht)

theorem radialMass_pos {t : ℝ} (ht : 0 < t) : 0 < radialMass n t := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (0 : ComplexVector n)) (contDiff_radialNumerator t).continuous
    (radialNumerator_hasCompactSupport ht) (radialNumerator_nonneg t)
  rw [radialNumerator_zero]
  exact one_ne_zero

theorem contDiff_radialKernel (t : ℝ) : ContDiff ℝ ∞ (radialKernel (n := n) t) :=
  (contDiff_radialNumerator t).div_const _

theorem radialKernel_nonneg {t : ℝ} (ht : 0 < t) (v : ComplexVector n) :
    0 ≤ radialKernel t v :=
  div_nonneg (radialNumerator_nonneg _ _) (radialMass_pos ht).le

theorem radialKernel_neg (t : ℝ) (v : ComplexVector n) : radialKernel t (-v) = radialKernel t v := by
  simp only [radialKernel, radialNumerator, norm_neg]

theorem radialKernel_rotate (t θ : ℝ) (v : ComplexVector n) :
    radialKernel t (Complex.exp (θ * Complex.I) • v) = radialKernel t v := by
  simp only [radialKernel, radialNumerator, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem radialKernel_support_subset_ball {t : ℝ} (ht : 0 < t) :
    Function.support (radialKernel (n := n) t) ⊆ Metric.ball 0 (2 * t) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  have hnorm : t ≤ ‖v‖ := by linarith [le_of_not_gt h]
  exact hv (by simp only [radialKernel, radialNumerator_zero_outer ht hnorm, zero_div])

theorem radialKernel_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (radialKernel (n := n) t) ⊆ Metric.closedBall 0 (2 * t) := by
  apply Metric.isClosed_closedBall.closure_subset_iff.mpr
  exact (radialKernel_support_subset_ball ht).trans Metric.ball_subset_closedBall

theorem radialKernel_hasCompactSupport {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (radialKernel (n := n) t) :=
  (isCompact_closedBall (0 : ComplexVector n) (2 * t)).of_isClosed_subset (isClosed_tsupport _)
    (radialKernel_tsupport_subset ht)

theorem integral_radialKernel {t : ℝ} (ht : 0 < t) :
    (∫ v : ComplexVector n, radialKernel t v) = 1 := by
  unfold radialKernel
  rw [integral_div]
  exact div_self (radialMass_pos ht).ne'

end Yau.Proofs.D04Aux
