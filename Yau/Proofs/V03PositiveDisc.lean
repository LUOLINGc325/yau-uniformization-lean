import Yau.Proofs.V03SmoothPowerSeries
import Yau.Proofs.V03FourierWeightedSummable
import Yau.Proofs.V03PositiveFourier
import Yau.Proofs.V03FourierAbsolute
import Yau.Proofs.V03CirclePeriod

/-! The genuine positive Fourier power series is holomorphic and complex
C∞ on the closed disc. Its boundary equals the native Fourier projection. -/

open scoped Topology ContDiff
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def positiveDiscProjection (u : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, circleFourier u (n : ℤ) * z ^ n

theorem positiveDiscProjection_contDiffOn {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) :
    ContDiffOn ℂ ∞ (positiveDiscProjection u) (Metric.closedBall 0 1) :=
  contDiffOn_powerSeries_closedDisc (fun k => circleFourier_pos_weighted_summable hu hp k)

theorem positiveDiscProjection_zero (u : ℝ → ℂ) :
    positiveDiscProjection u 0 = circleFourier u 0 := by
  have heq : (fun n : ℕ => circleFourier u (n : ℤ) * (0 : ℂ) ^ n) =
      Pi.single 0 (circleFourier u 0) := by
    funext n
    by_cases hn : n = 0
    · subst n; simp
    · simp [Pi.single_apply, hn]
  unfold positiveDiscProjection
  rw [heq]
  simp

theorem fourier_one_two_pi (θ : ℝ) :
    fourier 1 (θ : AddCircle (2 * Real.pi)) = circlePoint θ := by
  rw [fourier_coe_apply]
  unfold circlePoint
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  <;> ring

theorem positiveDiscProjection_boundary {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) (θ : ℝ) :
    positiveDiscProjection u (circlePoint θ) =
      positiveFourierSum (fun n : ℕ => circleFourier u (n : ℤ)) (θ : AddCircle (2 * Real.pi)) := by
  have hb : Summable (fun n : ℕ => circleFourier u (n : ℤ)) := by
    simpa only [Function.comp_def] using
      (circleFourier_summable hu hp).comp_injective Nat.cast_injective
  rw [positiveFourierSum_apply hb, fourier_one_two_pi]
  rfl

theorem closedDisc_trace_contDiff {H : ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall 0 1)) :
    ContDiff ℝ ∞ (fun θ => H (circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hh := (hH.restrict_scalars ℝ (circlePoint θ) (circlePoint_mem_closedBall θ)).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall t)
  exact contDiffWithinAt_univ.mp hh

end Yau.Blueprint.V03Proof
