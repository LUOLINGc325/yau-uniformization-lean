import Yau.LeafProofs.L05AutonomousEllipsoidAverage

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoEllipsoidMean {n : ℕ} (B : Space n ≃L[ℝ] Space n) (u : Point n → ℝ) (p : Point n) : ℝ :=
  autoSpatialAverage (autoLinearBallProbability B) (fun x => u (x,p.2)) p.1

def autoEllipsoidSecond {n : ℕ} (B : Space n ≃L[ℝ] Space n) (r : ℝ) (u : Point n → ℝ) (p : Point n) : ℝ :=
  (autoEllipsoidMean B u p-u p)/r^2

theorem autoLinearBallProbability_ball_ae {n : ℕ} (B : Space n ≃L[ℝ] Space n) {b : ℝ}
    (hB : ‖B.toContinuousLinearMap‖≤ b) :
    ∀ᵐ y ∂autoLinearBallProbability B, y∈Metric.closedBall (0 : Space n) b := by
  filter_upwards [autoLinearBallProbability_norm_ae B] with y hy
  simpa only [Metric.mem_closedBall,dist_zero_right] using hy.trans hB

/-- All local averages are genuinely integrable and continuous up to the closed top face. -/
theorem autoEllipsoidMean_continuous {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (B : Space n ≃L[ℝ] Space n) {b : ℝ}
    (hB : ‖B.toContinuousLinearMap‖≤ b)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) b, ∀ p∈Q, p+(y,0)∈unitClosed n) :
    (∀ p∈Q, Integrable (fun y => u (p.1+y,p.2)) (autoLinearBallProbability B)) ∧
      ContinuousOn (autoEllipsoidMean B u) Q := by
  let : IsProbabilityMeasure (autoLinearBallProbability B) := autoLinearBallProbability_isProbability B
  exact auto_probability_spatial_average_continuous hu (Metric.closedBall 0 b) (isCompact_closedBall _ _)
    (autoLinearBallProbability B) (autoLinearBallProbability_ball_ae B hB) hbuffer

theorem autoEllipsoidSecond_continuous {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : ContinuousOn u (unitClosed n)) (hQ : Q⊆unitClosed n) (B : Space n ≃L[ℝ] Space n)
    {b : ℝ} (hB : ‖B.toContinuousLinearMap‖≤ b) (r : ℝ)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) b, ∀ p∈Q, p+(y,0)∈unitClosed n) :
    ContinuousOn (autoEllipsoidSecond B r u) Q :=
  ((autoEllipsoidMean_continuous hu B hB hbuffer).2.sub (hu.mono hQ)).div_const _

/-- Only the first native difference clause is used: the positive mean is a subsolution. -/
theorem autoEllipsoidSecond_sub {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q) (hQU : Q⊆unitOpen n)
    {ell L : ℝ} (hell : 0< ell) (hL : ell≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsol : viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (B : Space n ≃L[ℝ] Space n) {b r : ℝ} (hB : ‖B.toContinuousLinearMap‖≤ b) (hr : 0< r)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) b, ∀ p∈Q, p+(y,0)∈unitOpen n) :
    viscositySub Q (fun H _ => pucciPlus ell L H) (fun _ => 0) (autoEllipsoidSecond B r u) := by
  let : IsProbabilityMeasure (autoLinearBallProbability B) := autoLinearBallProbability_isProbability B
  have hmean := auto_probability_spatial_average_sub hQ hell.le hL hF hE hC hu hsol.1
    (Metric.closedBall 0 b) (isCompact_closedBall _ _) (autoLinearBallProbability B)
    (autoLinearBallProbability_ball_ae B hB) hbuffer
  have huQ := hu.mono (hQU.trans unitOpen_subset_unitClosed)
  have hdiff := jet_autonomous_difference_sub hQ hell.le hL hE hmean.1 huQ hmean.2
    (viscositySuper_mono_domain hsol.2 hQU)
  have hscale := auto_pucci_sub_scale hell.le hL (inv_pos.mpr (sq_pos_of_pos hr)) hdiff
  convert hscale using 1
  funext p
  dsimp only [autoEllipsoidSecond,autoEllipsoidMean,autoSpatialAverage,Pi.sub_apply]
  rw [div_eq_mul_inv,mul_comm]

end Yau.LeafProofs.L05AutonomousAux
