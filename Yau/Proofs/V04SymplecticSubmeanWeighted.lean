import Yau.Proofs.V04SymplecticSubmeanMean

open scoped Topology ContDiff
open MeasureTheory Set
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

/-- A positive smooth periodic weight is realized by the SAME scalar outer
function on the closed disc, with its exact squared boundary modulus and center. -/
theorem exists_weight_outer {w : ℝ → ℝ} (hw : ∀ θ, 0 < w θ)
    (hc : ContDiff ℝ ∞ w) (hp : Function.Periodic w (2 * Real.pi)) :
    ∃ g : ℂ → ℂ, ContDiffOn ℂ ∞ g (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ θ, ‖g (circlePoint θ)‖ ^ 2 = w θ) ∧
      ‖g 0‖ ^ 2 = Real.exp (circleAverage (fun θ ↦ Real.log (w θ))) := by
  let q := fun θ ↦ (1 / 2 : ℝ) * Real.log (w θ)
  have hq : ContDiff ℝ ∞ q := contDiff_const.mul (hc.log (fun θ ↦ (hw θ).ne'))
  have hqp : Function.Periodic q (2 * Real.pi) := fun θ ↦ by simp only [q, hp θ]
  refine ⟨outerCandidate q 1, outerCandidate_contDiffOn hq hqp 1, ?_, ?_⟩
  · intro θ
    rw [outerCandidate_norm_boundary hq hqp]
    norm_num only [Nat.cast_one, one_mul]
    rw [pow_two, ← Real.exp_add]
    have he : q θ + q θ = Real.log (w θ) := by dsimp [q]; ring
    rw [he, Real.exp_log (hw θ)]
  · rw [outerCandidate_zero]
    norm_num only [Nat.cast_one, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [pow_two, ← Real.exp_add]
    congr 1
    rw [show circleAverage q = (1 / 2 : ℝ) * circleAverage (fun θ ↦ Real.log (w θ)) from
      circleAverage_const_mul_value _ _]
    ring

/-- Weighted square submean in the exact normalized circle average. The
outer proof handles zero center values and all empty matrix cases directly. -/
theorem weighted_closedDisc_square_submean {w : ℝ → ℝ} (hw : ∀ θ, 0 < w θ)
    (hc : ContDiff ℝ ∞ w) (hp : Function.Periodic w (2 * Real.pi))
    {f : ℂ → ℂ} (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    Real.exp (circleAverage (fun θ ↦ Real.log (w θ))) * ‖f 0‖ ^ 2 ≤
      circleAverage (fun θ ↦ w θ * ‖f (circlePoint θ)‖ ^ 2) := by
  obtain ⟨g, hg, hgb, hg0⟩ := exists_weight_outer hw hc hp
  have hs := closedDisc_square_submean (hg.mul hf)
  have hleft : ‖g 0 * f 0‖ ^ 2 =
      Real.exp (circleAverage (fun θ ↦ Real.log (w θ))) * ‖f 0‖ ^ 2 := by
    rw [norm_mul, mul_pow, hg0]
  have hright : (fun θ ↦ ‖g (circlePoint θ) * f (circlePoint θ)‖ ^ 2) =
      fun θ ↦ w θ * ‖f (circlePoint θ)‖ ^ 2 := by
    funext θ
    rw [norm_mul, mul_pow, hgb θ]
  rw [hleft, hright] at hs
  exact hs

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
