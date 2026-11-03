import Yau.LeafProofs.L05AutonomousEllipsoidViscosity
import Yau.LeafProofs.L05AutonomousMollifierAverage

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual finite probability and the original sup budget justify dominated convergence. -/
theorem autoEllipsoidMean_mollifier_tendsto {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j) (hlim : Tendsto eps atTop (𝓝 0)) (p : Point n) :
    Tendsto (fun j => autoEllipsoidMean B (autoSpatialMollify (eps j) (heps j) w) p) atTop
      (𝓝 (autoEllipsoidMean B w p)) := by
  let : IsProbabilityMeasure (autoLinearBallProbability B) := autoLinearBallProbability_isProbability B
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖w‖)
  · intro j
    exact ((autoSpatialMollify_continuous (eps j) (heps j) w hw).comp
      ((continuous_const.add continuous_id).prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
  · exact integrable_const _
  · exact fun j => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact autoSpatialMollify_abs_le (eps j) (heps j) w hw (p.1+y,p.2)
  · exact ae_of_all _ fun y => (autoSpatialMollify_uniform w hw eps heps hlim).tendsto_at (p.1+y,p.2)

/-- The limit is the original local second mean, not a mean of arbitrarily extended exterior data. -/
theorem autoEllipsoidSecond_mollifier_tendsto_original {n : ℕ} (B : Space n ≃L[ℝ] Space n) (r : ℝ)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) {u : Point n → ℝ}
    (hwu : EqOn w u (unitClosed n)) {b : ℝ} (hB : ‖B.toContinuousLinearMap‖≤ b)
    (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j) (hlim : Tendsto eps atTop (𝓝 0))
    (p : Point n) (hp : p∈unitClosed n)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) b, (p.1+y,p.2)∈unitClosed n) :
    Integrable (fun y => u (p.1+y,p.2)) (autoLinearBallProbability B) ∧
      Tendsto (fun j => autoEllipsoidSecond B r (autoSpatialMollify (eps j) (heps j) w) p) atTop
        (𝓝 (autoEllipsoidSecond B r u p)) := by
  let : IsProbabilityMeasure (autoLinearBallProbability B) := autoLinearBallProbability_isProbability B
  have heq : (fun y => w (p.1+y,p.2)) =ᵐ[autoLinearBallProbability B] (fun y => u (p.1+y,p.2)) := by
    filter_upwards [autoLinearBallProbability_ball_ae B hB] with y hy
    exact hwu (hbuffer y hy)
  have hiw : Integrable (fun y => w (p.1+y,p.2)) (autoLinearBallProbability B) :=
    Integrable.of_bound (w.continuous.comp ((continuous_const.add continuous_id).prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
      ‖w‖ (ae_of_all _ fun y => w.norm_coe_le_norm _)
  have hmean : autoEllipsoidMean B w p=autoEllipsoidMean B u p := integral_congr_ae heq
  have hmeanLim := autoEllipsoidMean_mollifier_tendsto B w hw eps heps hlim p
  rw [hmean] at hmeanLim
  have hpointLim := (autoSpatialMollify_uniform w hw eps heps hlim).tendsto_at p
  rw [hwu hp] at hpointLim
  exact ⟨hiw.congr heq,by simpa only [autoEllipsoidSecond] using (hmeanLim.sub hpointLim).div_const (r^2)⟩

end Yau.LeafProofs.L05AutonomousAux
