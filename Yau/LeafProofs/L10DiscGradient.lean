import Yau.LeafProofs.L10DiscGradientFTC

/-! The integral of the genuine kernel gradient is the genuine derivative
of the Green solution, including within derivatives on the closed disc. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discGreenSolution_fderiv {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    fderiv ℝ (discGreenSolution f) z = discGreenDerivative f z := by
  have hu : DifferentiableAt ℝ (discGreenSolution f) z :=
    ((discGreenSolution_contDiffOn_interior hf).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  apply ContinuousLinearMap.ext
  intro v
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hu0 : HasFDerivAt (discGreenSolution f)
      (fderiv ℝ (discGreenSolution f) z) (z + (0 : ℝ) • v) := by
    simpa using hu.hasFDerivAt
  have hactual : HasDerivAt (fun t : ℝ => discGreenSolution f (z + t • v))
      (fderiv ℝ (discGreenSolution f) z v) 0 := by
    simpa only [Function.comp_def] using hu0.comp_hasDerivAt (0 : ℝ) hline
  exact hactual.unique (discGreenSolution_hasDerivAt_affine hf.continuousOn hz v)

theorem discGreenInteriorGradient : DiscGreenInteriorGradientGap := by
  intro f hf z hz
  exact discGreenSolution_fderiv hf hz

theorem discGreenSolution_hasFDerivWithinAt {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasFDerivWithinAt (discGreenSolution f) (discGreenDerivative f z)
      (Metric.closedBall (0 : ℂ) 1) z :=
  discGreenSolution_hasFDerivWithinAt_of_interiorGradient discGreenInteriorGradient hf hz

theorem discGreenSolution_fderivWithin {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    fderivWithin ℝ (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) z =
      discGreenDerivative f z :=
  (discGreenSolution_hasFDerivWithinAt hf hz).fderivWithin (disc_closedBall_uniqueDiffOn z hz)

theorem discGreenSolution_contDiffOn_one {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ 1 (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) :=
  discGreenSolution_contDiffOn_one_of_interiorGradient discGreenInteriorGradient hf

end Yau.LeafProofs
