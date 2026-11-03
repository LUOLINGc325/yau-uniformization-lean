import Yau.Proofs.V03Elementary
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! A holomorphic interior derivative with an actual continuous extension
to the closed ball is the complex within derivative at its boundary. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivWithinAt_complex_closedBall {f : E → F} {A : E → E →L[ℂ] F}
    {c x : E} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hcont : ContinuousOn f (Metric.closedBall c R))
    (hA : ContinuousOn A (Metric.closedBall c R))
    (hEq : ∀ y ∈ Metric.ball c R, fderiv ℂ f y = A y)
    (hx : x ∈ Metric.closedBall c R) :
    HasFDerivWithinAt f (A x) (Metric.closedBall c R) x := by
  have hAc : ContinuousWithinAt (fun y => (A y).restrictScalars ℝ)
      (Metric.closedBall c R) x :=
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn hA) x hx
  have hlim : Tendsto (fderiv ℝ f) (𝓝[Metric.ball c R] x)
      (𝓝 ((A x).restrictScalars ℝ)) := by
    apply (hAc.mono Metric.ball_subset_closedBall).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hd : DifferentiableAt ℂ f y := (hf y hy).differentiableAt (Metric.isOpen_ball.mem_nhds hy)
    exact ((hd.fderiv_restrictScalars (𝕜 := ℝ)).trans
      (congrArg (fun L : E →L[ℂ] F => L.restrictScalars ℝ) (hEq y hy))).symm
  have hreal : HasFDerivWithinAt f ((A x).restrictScalars ℝ) (closure (Metric.ball c R)) x :=
    hasFDerivWithinAt_closure_of_tendsto_fderiv (hf.restrictScalars ℝ) (convex_ball c R) Metric.isOpen_ball
      (fun y hy => (hcont y (by simpa only [closure_ball c hR.ne'] using hy)).mono
        Metric.ball_subset_closedBall) hlim
  have hc : HasFDerivWithinAt f (A x) (closure (Metric.ball c R)) x :=
    hreal.of_restrictScalars ℝ rfl
  simpa only [closure_ball c hR.ne'] using hc

end Yau.Blueprint.V03Proof
