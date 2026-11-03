import Yau.Proofs.V03Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Repeated native integration by parts supplies arbitrarily high Fourier
coefficient decay for the actual smooth periodic traces. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem periodic_deriv {u : ℝ → ℂ} {T : ℝ} (hp : Function.Periodic u T) :
    Function.Periodic (deriv u) T := by
  have heq : (fun θ => u (θ + T)) = u := funext hp
  intro θ
  rw [← deriv_comp_add_const u T θ, heq]

theorem periodic_iteratedDeriv {u : ℝ → ℂ} {T : ℝ} (hp : Function.Periodic u T) (m : ℕ) :
    Function.Periodic (iteratedDeriv m u) T := by
  induction m with
  | zero => simpa using hp
  | succ m ih => simpa only [iteratedDeriv_succ] using periodic_deriv ih

theorem circleFourier_iteratedDeriv {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) {k : ℤ} (hk : k ≠ 0) (m : ℕ) :
    circleFourier u k = (Complex.I * (k : ℂ))⁻¹ ^ m *
      circleFourier (iteratedDeriv m u) k := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hu_m : ContDiff ℝ (m + 1) u := hu.of_le (by simp)
      have hstep := circleFourier_of_hasDerivAt (u := iteratedDeriv m u)
        (u' := iteratedDeriv (m + 1) u) hk
        (fun θ _ => by
          simpa only [iteratedDeriv_succ] using
            (ContDiff.differentiable_iteratedDeriv' m hu_m θ).hasDerivAt)
        ((hu.continuous_iteratedDeriv (m + 1) (by simp)).intervalIntegrable _ _)
        (by simpa using periodic_iteratedDeriv hp m 0)
      rw [ih, hstep, pow_succ]
      ring

theorem circleFourier_norm_iteratedDeriv {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) {k : ℤ} (hk : k ≠ 0) (m : ℕ) :
    ‖circleFourier u k‖ = |(k : ℝ)|⁻¹ ^ m * ‖circleFourier (iteratedDeriv m u) k‖ := by
  rw [circleFourier_iteratedDeriv hu hp hk m, norm_mul, norm_pow, norm_inv, norm_mul,
    Complex.norm_I, one_mul]
  congr 2
  rw [← Complex.ofReal_intCast]
  simp only [Complex.norm_real, Real.norm_eq_abs]

end Yau.Blueprint.V03Proof
