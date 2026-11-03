import Yau.Proofs.V04ScalarFejerError
import Yau.Proofs.V04FejerPolynomial
import Yau.Proofs.V03PeriodicCircle

/-! The finite circle polynomial is exactly the frozen Fejer mean, with
period 2pi and normalized average. This bridge retains the original
Fourier and matrix-entry conventions. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem circleAverage_coe (f : AddCircle (2 * Real.pi) → ℝ) :
    circleAverage (fun θ => f (θ : AddCircle (2 * Real.pi))) =
      ∫ x : AddCircle (2 * Real.pi), f x ∂haarAddCircle := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 f]
  simp only [zero_add, smul_eq_mul, circleAverage]

theorem fourier_twopi_coe (k : ℤ) (θ : ℝ) :
    fourier k (θ : AddCircle (2 * Real.pi)) = Complex.exp ((k : ℂ) * θ * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  <;> ring

variable {n : ℕ}

theorem fejerMean_entry_eq_scalarFejer (A : ℝ → CotangentMatrix n)
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi))
    (P : ℕ) (θ : ℝ) (i k : CotangentIndex n) :
    fejerMean A P θ i k = scalarFejer (hp i k).lift P (θ : AddCircle (2 * Real.pi)) := by
  rw [fejerMean_apply, scalarFejer]
  apply Finset.sum_congr rfl
  intro l hl
  rw [fejerMultiplier, if_pos hl, ← circleFourier_eq_periodic_lift (hp i k), fourier_twopi_coe]
  push_cast
  ring

theorem fejerMean_entry_continuous (A : ℝ → CotangentMatrix n)
    (P : ℕ) (i k : CotangentIndex n) : Continuous (fun θ => fejerMean A P θ i k) := by
  simp only [fejerMean_apply]
  apply continuous_finsetSum
  intro l _
  fun_prop

theorem fejerMean_entry_error_average (A : ℝ → CotangentMatrix n)
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi))
    (P : ℕ) (i k : CotangentIndex n) :
    circleAverage (fun θ => ‖fejerMean A P θ i k - A θ i k‖ ^ 2) =
      ∫ x : AddCircle (2 * Real.pi),
        ‖scalarFejer (hp i k).lift P x - (hp i k).lift x‖ ^ 2 ∂haarAddCircle := by
  rw [← circleAverage_coe]
  apply congrArg circleAverage
  funext θ
  rw [fejerMean_entry_eq_scalarFejer A hp, Function.Periodic.lift_coe]

theorem fejerMean_entry_error_ennreal (A : ℝ → CotangentMatrix n)
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi))
    (P : ℕ) (i k : CotangentIndex n) :
    ENNReal.ofReal (circleAverage (fun θ => ‖fejerMean A P θ i k - A θ i k‖ ^ 2)) ≤
      ENNReal.ofReal (((P : ℝ) + 1)⁻¹) *
        boundaryDSq (fun θ (_ : Unit) => A θ i k) := by
  rw [fejerMean_entry_error_average A hp,
    circleDirichlet_periodic_lift (hp i k)]
  exact scalarFejer_error_ennreal (periodic_lift_continuous (hp i k) (hA i k)) P

end Yau.Blueprint.V04Proof
