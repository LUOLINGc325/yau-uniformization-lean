import Yau.Proofs.V03FourierEnergy

/-! The actual angular derivative has the Fourier multiplier ik at every
integer frequency, with the zero mode supplied by the genuine FTC. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_derivative_all {u u' : ℝ → ℂ}
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hp : u (2 * Real.pi) = u 0) (k : ℤ) :
    circleFourier u' k = Complex.I * (k : ℂ) * circleFourier u k := by
  by_cases hk : k = 0
  · subst k
    simp only [circleFourier, Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero,
      one_mul, mul_zero, zero_mul]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hu hu', hp, sub_self, mul_zero]
  · have hc := circleFourier_of_hasDerivAt hk hu hu' hp
    have hne : Complex.I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem circleFourier_negative_I_derivative {u u' : ℝ → ℂ}
    (hu : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (u' θ) θ)
    (hu' : IntervalIntegrable u' volume 0 (2 * Real.pi))
    (hp : u (2 * Real.pi) = u 0) (k : ℤ) :
    circleFourier (fun θ => -Complex.I * u' θ) k = (k : ℂ) * circleFourier u k := by
  rw [circleFourier_const_mul, circleFourier_derivative_all hu hu' hp]
  have he : -Complex.I * (Complex.I * (k : ℂ) * circleFourier u k) =
      (-Complex.I * Complex.I) * ((k : ℂ) * circleFourier u k) := by ring
  rw [he]
  norm_num

end Yau.Blueprint.V03Proof
