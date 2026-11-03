import Yau.Proofs.V03Fourier
import Yau.Proofs.V03Energy

/-! The zero Fourier mode is the actual normalized mean, and the original
outer center has exactly the required real positive normalization. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_ofReal_zero (q : ℝ → ℝ) :
    circleFourier (fun θ => (q θ : ℂ)) 0 = (circleAverage q : ℂ) := by
  unfold circleFourier circleAverage
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul,
    intervalIntegral.integral_ofReal, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_ofNat]

theorem circleAverage_const_mul_value (c : ℝ) (q : ℝ → ℝ) :
    circleAverage (fun θ => c * q θ) = c * circleAverage q := by
  unfold circleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem circleAverage_log_wallPower {n q : ℕ} {X : KahlerManifold n}
    (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    circleAverage (fun θ => Real.log (wallPower d j a (F.f (circlePoint θ)))) =
      (a : ℝ) * circleAverage (logTrace d j F.f) := by
  simp only [wallPower, Real.log_pow]
  exact circleAverage_const_mul_value (a : ℝ) _

theorem outerCenter_eq_exp_logTrace {n q : ℕ} {X : KahlerManifold n}
    (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    outerCenter d j a F = Real.exp ((a : ℝ) * circleAverage (logTrace d j F.f)) := by
  unfold outerCenter
  rw [circleAverage_log_wallPower]

end Yau.Blueprint.V03Proof
