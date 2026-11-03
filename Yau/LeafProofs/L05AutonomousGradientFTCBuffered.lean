import Yau.LeafProofs.L05AutonomousGradientFTCLimit
import Yau.LeafProofs.L05AutonomousMollifierSpace

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Interval BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic
local instance autoGradientFTCBuffered_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoGradientFTCBuffered_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoGradientFTCBuffered_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoGradientFTCBuffered_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The two actual uniform jet limits of the canonical smoothing give the
literal gradient FTC at every closed time, including zero. -/
theorem auto_gradient_ftc_from_uniform_spatial_jets {n : ℕ} {r : ℝ}
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j)
    (H : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ))
    (hGrad : TendstoUniformlyOn (fun j => spatialD (autoSpatialMollify (eps j) (heps j) w))
      (spatialD w) atTop (autoClosed (0 : Space n) r 0))
    (hHess : TendstoUniformlyOn
      (fun j p => fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify (eps j) (heps j) w (y,p.2))) p.1)
      H atTop (autoClosed (0 : Space n) r 0)) :
    ∀ t∈Icc (-(r^2)) 0, ∀ x∈Metric.closedBall (0 : Space n) r,
      ∀ y∈Metric.closedBall (0 : Space n) r,
        spatialD w (y,t)-spatialD w (x,t)=
          ∫ s in (0 : ℝ)..1, H (x+s • (y-x),t) (y-x) := by
  intro t ht x hx y hy
  let f : ℕ → Space n → ℝ := fun j z => autoSpatialMollify (eps j) (heps j) w (z,t)
  have hSlice : ∀ z∈Metric.closedBall (0 : Space n) r, (z,t)∈autoClosed (0 : Space n) r 0 := by
    intro z hz
    exact ⟨hz,by simpa only [zero_sub] using ht⟩
  have hFirst := (hGrad.comp (fun z : Space n => (z,t))).mono hSlice
  have hSecond := (hHess.comp (fun z : Space n => (z,t))).mono hSlice
  exact auto_gradient_ftc_limit f
    (fun j => autoSpatialMollify_spatial_contDiff (eps j) (heps j) w hw t)
    (fun z => spatialD w (z,t)) (fun z => H (z,t)) hFirst hSecond hx hy

end Yau.LeafProofs.L05AutonomousAux
