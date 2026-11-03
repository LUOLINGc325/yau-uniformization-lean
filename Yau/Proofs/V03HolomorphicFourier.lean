import Yau.Proofs.V03Fourier
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Negative Fourier modes of the actual boundary trace of a holomorphic
closed disc vanish by the native Cauchy-Goursat theorem. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleIntegral_monomial_eq_fourier (H : ℂ → ℂ) (m : ℕ) :
    (∮ z in C(0, 1), z ^ m * H z) =
      (2 * Real.pi * Complex.I : ℂ) *
        circleFourier (fun θ => H (circlePoint θ)) (-((m + 1 : ℕ) : ℤ)) := by
  have hcircle : circleMap 0 1 = circlePoint := by
    funext θ
    simp [circleMap, circlePoint]
  have hexp (θ : ℝ) :
      Complex.exp (-(-((m + 1 : ℕ) : ℤ) : ℂ) * θ * Complex.I) =
        circlePoint θ ^ (m + 1) := by
    rw [circlePoint, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold circleIntegral circleFourier
  simp only [deriv_circleMap]
  simp only [hcircle, smul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_neg]
  simp only [Int.cast_neg, Int.cast_natCast, neg_neg] at hexp
  simp_rw [hexp]
  have hpoint : (fun θ : ℝ => circlePoint θ * Complex.I * (circlePoint θ ^ m * H (circlePoint θ))) =
      (fun θ => Complex.I * (circlePoint θ ^ (m + 1) * H (circlePoint θ))) := by
    funext θ
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

theorem holomorphic_boundary_fourier_negSucc {H : ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) (m : ℕ) :
    circleFourier (fun θ => H (circlePoint θ)) (-((m + 1 : ℕ) : ℤ)) = 0 := by
  have hprod : ContDiffOn ℂ ∞ (fun z => z ^ m * H z) (Metric.closedBall 0 1) :=
    (contDiffOn_id.pow m).mul hH
  have hzero := ((hprod.differentiableOn (by simp)).diffContOnCl_ball Set.Subset.rfl).circleIntegral_eq_zero
    (by norm_num : (0 : ℝ) ≤ 1)
  rw [circleIntegral_monomial_eq_fourier] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

end Yau.Blueprint.V03Proof
