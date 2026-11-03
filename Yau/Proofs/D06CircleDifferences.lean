import Yau.Proofs.D06HardyFourier
import Yau.Proofs.D06NormEstimates

/-! Haar-averaged translation differences, with exact evenness available for
measurable traces before closed-disc smoothness. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint
variable {r : ℕ}

def circleDifference (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (θ : HardyCircle) : ℝ :=
  ∫ t, frobSq (A (t + θ) - A t) ∂hardyCircleMeasure

theorem circleDifference_nonneg (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (θ : HardyCircle) :
    0 ≤ circleDifference A θ := integral_nonneg (fun _ => frobSq_nonneg _)

theorem circleDifference_even (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (θ : HardyCircle) :
    circleDifference A (-θ) = circleDifference A θ := by
  calc
    _ = ∫ t, frobSq (A ((t + θ) + -θ) - A (t + θ)) ∂hardyCircleMeasure :=
      (integral_add_right_eq_self (μ := hardyCircleMeasure)
        (fun t => frobSq (A (t + -θ) - A t)) θ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [add_neg_cancel_right, frobSq_sub_comm]

theorem circleDifference_sharp_of_symmetric_energy
    (A L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (E : HardyCircle → ℝ)
    (C K : ℝ) (hC : 0 ≤ C)
    (hAE : ∀ θ, circleDifference A θ ≤ C * E θ)
    (hEL : ∀ θ, E θ + E (-θ) ≤ K * circleDifference L θ) (θ : HardyCircle) :
    circleDifference A θ ≤ C * K / 2 * circleDifference L θ := by
  have hp := hAE θ
  have hn := hAE (-θ)
  rw [circleDifference_even] at hn
  have he := mul_le_mul_of_nonneg_left (hEL θ) hC
  nlinarith

end Yau.NodeProofs.D06Aux
