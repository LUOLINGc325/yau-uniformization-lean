import Yau.Proofs.V03DiscLaplacianGreen
import Yau.Proofs.V03HolomorphicNormLaplacian

/-! The actual holomorphic norm area is exactly its boundary Hermitian
current. Only the original smooth closed-disc regularity is used. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def normBoundaryCurrent (f : ℂ → H) (θ : ℝ) : ℝ :=
  (inner ℂ (f (Yau.Blueprint.circlePoint θ))
    ((Yau.Blueprint.circlePoint θ) • closedDiscDerivative f (Yau.Blueprint.circlePoint θ))).re

theorem normDiscArea_eq_boundary_current {f : ℂ → H}
    (hf : ContDiffOn ℂ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    normDiscArea f = ENNReal.ofReal (∫ θ in (-Real.pi)..Real.pi, normBoundaryCurrent f θ) := by
  have hu : ContDiffOn ℝ ∞ (fun z => ‖f z‖ ^ 2) (Metric.closedBall (0 : ℂ) 1) :=
    (hf.restrict_scalars ℝ).norm_sq ℂ
  have hreal : (∫ z in Metric.ball (0 : ℂ) 1, 2 * ‖closedDiscDerivative f z‖ ^ 2) =
      (1 / 2 : ℝ) * (∫ z in Metric.ball (0 : ℂ) 1, closedLaplacian (fun w => ‖f w‖ ^ 2) z) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    have hnhds : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
    have hfAt : ContDiffAt ℂ 2 f z := (hf.contDiffAt hnhds).of_le (by simp)
    rw [closedLaplacian_holomorphic_norm_sq hz hfAt, closedDiscDerivative,
      fderivWithin_of_mem_nhds hnhds]
    ring
  have hb (θ : ℝ) : closedRealGradient (fun z => ‖f z‖ ^ 2) (Yau.Blueprint.circlePoint θ)
      (Yau.Blueprint.circlePoint θ) = 2 * normBoundaryCurrent f θ := by
    rw [closedRealGradient_holomorphic_norm_sq hf (circlePoint_mem_closedBall θ)]
    have hd : fderivWithin ℂ f (Metric.closedBall 0 1) (Yau.Blueprint.circlePoint θ)
        (Yau.Blueprint.circlePoint θ) = (Yau.Blueprint.circlePoint θ) •
          closedDiscDerivative f (Yau.Blueprint.circlePoint θ) := by
      simpa only [smul_eq_mul, mul_one, closedDiscDerivative] using
        (fderivWithin ℂ f (Metric.closedBall 0 1) (Yau.Blueprint.circlePoint θ)).map_smul
          (Yau.Blueprint.circlePoint θ) (1 : ℂ)
    rw [hd]
    rfl
  have ha := normDiscArea_radial_eq_integral hf (r := 1) (by simp)
  simp only [Complex.ofReal_one, one_mul, radialEuclideanDensity, one_smul] at ha
  rw [hreal, integral_closedLaplacian_eq_boundary hu] at ha
  simp_rw [hb] at ha
  rw [intervalIntegral.integral_const_mul] at ha
  have hc (x : ℝ) : (1 / 2 : ℝ) * (2 * x) = x := by ring
  simpa only [hc] using ha

end Yau.Blueprint.V03Proof
