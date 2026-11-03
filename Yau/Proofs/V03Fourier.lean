import Yau.Proofs.V03Elementary
import Mathlib.Analysis.Fourier.AddCircle

/-! The Fourier coefficients used by V03 have exactly the normalized
`AddCircle` convention with period `2π`. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_eq_fourierCoeffOn (u : ℝ → ℂ) (k : ℤ) :
    circleFourier u k = fourierCoeffOn
      (by positivity : (0 : ℝ) < 2 * Real.pi) u k := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul, one_div, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  unfold circleFourier
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [fourier_coe_apply, Int.cast_neg]
  congr 2
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  <;> ring

theorem circleFourier_const_mul (u : ℝ → ℂ) (c : ℂ) (k : ℤ) :
    circleFourier (fun θ => c * u θ) k = c * circleFourier u k := by
  simp only [circleFourier_eq_fourierCoeffOn]
  exact fourierCoeffOn.const_mul u c k _

theorem circleFourier_add {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v) (k : ℤ) :
    circleFourier (fun θ => u θ + v θ) k =
      circleFourier u k + circleFourier v k := by
  unfold circleFourier
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add]
  · ring
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
      Complex.exp (-(k : ℂ) * θ * Complex.I) * u θ)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun θ : ℝ =>
      Complex.exp (-(k : ℂ) * θ * Complex.I) * v θ)).intervalIntegrable _ _

theorem circleFourier_sub {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v) (k : ℤ) :
    circleFourier (fun θ => u θ - v θ) k =
      circleFourier u k - circleFourier v k := by
  simpa only [Pi.mul_apply, neg_one_mul, sub_eq_add_neg] using
    (circleFourier_add hu (continuous_const.mul hv) k).trans
      (congrArg (fun z => circleFourier u k + z) (circleFourier_const_mul v (-1) k))

theorem circleFourier_of_hasDerivAt {u u' : ℝ → ℂ} {k : ℤ} (hk : k ≠ 0)
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hperiod : u (2 * Real.pi) = u 0) :
    circleFourier u k = (Complex.I * (k : ℂ))⁻¹ * circleFourier u' k := by
  rw [circleFourier_eq_fourierCoeffOn, fourierCoeffOn_of_hasDerivAt _ hk hu hu']
  simp only [hperiod, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero,
    ← circleFourier_eq_fourierCoeffOn]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  push_cast
  field_simp
  <;> ring

theorem circleFourier_parseval {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :
    HasSum (fun k : ℤ => ‖circleFourier u k‖ ^ 2)
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖u θ‖ ^ 2) := by
  simpa only [circleFourier_eq_fourierCoeffOn, sub_zero, smul_eq_mul] using
    hasSum_sq_fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) hu

end Yau.Blueprint.V03Proof
