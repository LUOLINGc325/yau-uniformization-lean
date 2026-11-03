import Yau.Proofs.V03PeriodicInnerParseval
import Yau.Proofs.V03FourierDerivativeAll
import Yau.Proofs.V03Dirichlet

/-! A genuine periodic C¹ trace with no negative modes has its actual
half-order seminorm equal to its exact boundary derivative current. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_eq_positive_current {u u' : ℝ → ℂ}
    (hu : Continuous u) (hu' : Continuous u')
    (hup : Function.Periodic u (2 * Real.pi))
    (hu'p : Function.Periodic u' (2 * Real.pi))
    (hd : ∀ θ, HasDerivAt u (u' θ) θ)
    (hneg : ∀ k : ℤ, k < 0 → circleFourier u k = 0) :
    boundaryDSq (fun θ (_ : Unit) => u θ) =
      ENNReal.ofReal (circleAverage (fun θ => (star (u θ) * (-Complex.I * u' θ)).re)) := by
  have hperiod : u (2 * Real.pi) = u 0 := by simpa only [zero_add] using hup 0
  have hi : IntervalIntegrable u' volume 0 (2 * Real.pi) := hu'.intervalIntegrable _ _
  have hv : Continuous (fun θ => -Complex.I * u' θ) := continuous_const.mul hu'
  have hvp : Function.Periodic (fun θ => -Complex.I * u' θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [hu'p θ]
  have hh := periodic_parseval_inner_real hu hv hup hvp
  have hcoeff (k : ℤ) : (star (circleFourier u k) *
      circleFourier (fun θ => -Complex.I * u' θ) k).re =
      |(k : ℝ)| * ‖circleFourier u k‖ ^ 2 := by
    rw [circleFourier_negative_I_derivative (fun θ _ => hd θ) hi hperiod]
    by_cases hk : k < 0
    · rw [hneg k hk]
      simp
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_not_gt hk
      rw [abs_of_nonneg hk0]
      have he : star (circleFourier u k) * ((k : ℂ) * circleFourier u k) =
          (k : ℂ) * (star (circleFourier u k) * circleFourier u k) := by ring
      rw [he, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero]
  simp_rw [hcoeff] at hh
  rw [boundaryDSq_singleton_eq, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hh.summable,
    hh.tsum_eq]

end Yau.Blueprint.V03Proof
