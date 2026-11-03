import Yau.Proofs.V03PolarGradient

/-! The genuine twice-within derivative extends the real Laplacian to the
closed disc and agrees with ordinary derivatives at every interior point. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

def closedRealHessian (u : ℂ → ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  fderivWithin ℝ (closedRealGradient u) (Metric.closedBall 0 1) z

def closedLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  closedRealHessian u z 1 1 + closedRealHessian u z Complex.I Complex.I

theorem closedRealHessian_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (closedRealHessian u) (Metric.closedBall (0 : ℂ) 1) :=
  (closedRealGradient_contDiffOn hu).fderivWithin uniqueDiffOn_real_closedDisc (m := ∞) (by simp)

theorem closedLaplacian_contDiffOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (closedLaplacian u) (Metric.closedBall (0 : ℂ) 1) :=
  (((closedRealHessian_contDiffOn hu).clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    (((closedRealHessian_contDiffOn hu).clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem closedRealHessian_eq {u : ℂ → ℝ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    closedRealHessian u z = fderiv ℝ (fderiv ℝ u) z := by
  have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  rw [closedRealHessian, fderivWithin_of_mem_nhds hnhds,
    (closedRealGradient_eventually_eq hz).fderiv_eq]

theorem closedLaplacian_eq {u : ℂ → ℝ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    closedLaplacian u z = fderiv ℝ (fderiv ℝ u) z 1 1 +
      fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I := by
  simp only [closedLaplacian, closedRealHessian_eq hz]

end Yau.Blueprint.V03Proof
