import Yau.Proofs.D06CircleConjugation
import Yau.Proofs.D06SmoothSourceDifferences

/-! Smooth periodic functions have all actual Fourier Sobolev orders, via
their genuine angular derivatives and the existing integration-by-parts formula. -/

open scoped Topology ContDiff Interval
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

def periodicScalarMap (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi))
    (hc : Continuous f) : C(HardyCircle, ℂ) where
  toFun := hp.lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    apply hc.quotient_liftOn'

def periodicScalarLp (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi))
    (hc : Continuous f) : CircleL2 :=
  ContinuousMap.toLp 2 hardyCircleMeasure ℂ (periodicScalarMap f hp hc)

theorem periodic_lift_fourierCoeffOn (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi)) (n : ℤ) :
    fourierCoeff (hp.lift : HardyCircle → ℂ) n = fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
  simp only [zero_add, Function.Periodic.lift_coe, fourier_coe_apply, sub_zero]

theorem periodicScalarLp_coeff (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi))
    (hc : Continuous f) (n : ℤ) :
    circleCoeff (periodicScalarLp f hp hc) n = fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n := by
  rw [circleCoeff_eq_fourierCoeff]
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) hardyCircleMeasure (periodicScalarMap f hp hc)
  exact (congrFun (fourierCoeff_congr_ae h) n).trans (periodic_lift_fourierCoeffOn f hp n)

theorem periodic_fourierCoeffOn_deriv (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi))
    (hs : ContDiff ℝ ∞ f) (n : ℤ) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) (deriv f) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n := by
  have hd : Differentiable ℝ f := hs.differentiable (by simp)
  have hcont : Continuous (deriv f) := hs.continuous_deriv (by simp)
  have hper : f (2 * Real.pi) = f 0 := by simpa only [zero_add] using hp 0
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, Int.cast_zero, mul_zero, zero_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) (hcont.intervalIntegrable _ _), hper, sub_self, smul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt (by positivity : (0 : ℝ) < 2 * Real.pi) hn
      (fun x _ => (hd x).hasDerivAt) (hcont.intervalIntegrable _ _)
    rw [hper, sub_self, mul_zero, zero_sub] at h
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
    push_cast at h
    field_simp at h
    apply (mul_left_injective₀ (show (2 * (Real.pi : ℂ)) ≠ 0 by exact mul_ne_zero (by norm_num) hπ))
    linear_combination -h

theorem periodicScalarLp_weakDerivative (f : ℝ → ℂ) (hp : Function.Periodic f (2 * Real.pi))
    (hs : ContDiff ℝ ∞ f) :
    CircleWeakDerivative (periodicScalarLp f hp hs.continuous)
      (periodicScalarLp (deriv f)
        (periodic_deriv_real_complex f _ hp (hs.differentiable (by simp)))
        (hs.continuous_deriv (by simp))) := by
  intro n
  rw [periodicScalarLp_coeff, periodicScalarLp_coeff]
  exact periodic_fourierCoeffOn_deriv f hp hs n

theorem periodicScalarLp_sobolev (k : ℕ) (f : ℝ → ℂ)
    (hp : Function.Periodic f (2 * Real.pi)) (hs : ContDiff ℝ ∞ f) :
    CircleSobolev k (periodicScalarLp f hp hs.continuous) := by
  induction k generalizing f with
  | zero => exact circleSobolev_zero _
  | succ k ih =>
    have hds : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hs).2
    have hdp := periodic_deriv_real_complex f (2 * Real.pi) hp (hs.differentiable (by simp))
    exact circleSobolev_succ_of_derivative k (periodicScalarLp_weakDerivative f hp hs)
      (ih f hp hs) (ih (deriv f) hdp hds)

end Yau.NodeProofs.D06Aux
