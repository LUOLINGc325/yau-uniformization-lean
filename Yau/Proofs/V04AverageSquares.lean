import Yau.Proofs.V04NegativeMomentLimits

/-! Cauchy-Schwarz for the actual normalized real circle average follows
from the integral of a nonnegative square, after proving continuity. -/

open MeasureTheory
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem circleAverage_add_of_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ => f θ + g θ) = circleAverage f + circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem circleAverage_const_mul (c : ℝ) (f : ℝ → ℝ) :
    circleAverage (fun θ => c * f θ) = c * circleAverage f := by
  unfold circleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem circleAverage_square_le (f : ℝ → ℝ) (hf : Continuous f) :
    circleAverage f ^ 2 ≤ circleAverage (fun θ => f θ ^ 2) := by
  let m := circleAverage f
  have hpow : Continuous (fun θ => f θ ^ 2) := hf.pow 2
  have hmul : Continuous (fun θ => (-2 * m) * f θ) := continuous_const.mul hf
  have hadd : Continuous (fun θ => f θ ^ 2 + (-2 * m) * f θ) := hpow.add hmul
  have heq : circleAverage (fun θ => (f θ - m) ^ 2) =
      circleAverage (fun θ => f θ ^ 2) - m ^ 2 := by
    have hfun : (fun θ => (f θ - m) ^ 2) =
        (fun θ => (f θ ^ 2 + (-2 * m) * f θ) + m ^ 2) := by funext θ; ring
    rw [hfun, circleAverage_add_of_continuous hadd continuous_const,
      circleAverage_add_of_continuous hpow hmul,
      circleAverage_const_mul, circleAverage_const_value]
    dsimp [m]
    ring
  have hn := circleAverage_nonneg (fun θ => sq_nonneg (f θ - m))
  rw [heq] at hn
  exact sub_nonneg.mp hn

theorem circleAverage_le_sqrt_square (f : ℝ → ℝ) (hf : Continuous f) (hnon : ∀ θ, 0 ≤ f θ) :
    circleAverage f ≤ Real.sqrt (circleAverage (fun θ => f θ ^ 2)) := by
  have hs := circleAverage_square_le f hf
  have hn := circleAverage_nonneg (fun θ => sq_nonneg (f θ))
  exact (sq_le_sq₀ (circleAverage_nonneg hnon) (Real.sqrt_nonneg _)).mp
    (hs.trans_eq (Real.sq_sqrt hn).symm)

end Yau.Blueprint.V04Proof
