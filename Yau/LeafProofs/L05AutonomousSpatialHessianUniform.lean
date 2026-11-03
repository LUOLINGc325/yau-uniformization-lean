import Yau.LeafProofs.L05AutonomousSpatialHessianOperator
import Yau.LeafProofs.L05AutonomousSpatialAverageUniform

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic
local instance autoSpatialHessianUniform_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianUniform_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianUniform_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoSpatialHessianUniform_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- On a genuine smaller closed cylinder, the ACTUAL spatial Hessians of the
canonical spatial mollifications converge uniformly in operator norm to the
continuous symmetric representative. The top time is included. -/
theorem auto_spatial_mollify_hessian_uniform {n : ℕ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ))
    (H : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ)) (hH : StronglyMeasurable H)
    (hHC : ContinuousOn H (autoClosed (0 : Space n) R 0))
    (hSym : ∀ p, ∀ v z, H p v z=H p z v)
    (steps : ℕ → ℝ) (hpos : ∀ j, 0 < steps j) (hzero : Tendsto steps atTop (𝓝 0))
    {B D : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ e : Space n, ‖e‖=1 → ∀ j, ∀ p∈autoOpen (0 : Space n) R 0,
      |autoSecond w e (steps j) p| ≤ B)
    (hLimit : ∀ e : Space n, ‖e‖=1 →
      ∀ᵐ p ∂((volume : Measure (Point n)).restrict (autoOpen (0 : Space n) R 0)),
        Tendsto (fun j => autoSecond w e (steps j) p) atTop (𝓝 (H p e e)))
    (hHBound : ∀ p∈autoClosed (0 : Space n) R 0, ‖H p‖ ≤ D)
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j) (hepszero : Tendsto eps atTop (𝓝 0))
    (hepsBuffer : ∀ j, r+eps j < R) :
    TendstoUniformlyOn
      (fun j p => fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify (eps j) (heps j) w (y,p.2))) p.1)
      H atTop (autoClosed (0 : Space n) r 0) := by
  have hR : 0 < R := hr.trans hrR
  have hSub : autoClosed (0 : Space n) r 0 ⊆ autoClosed (0 : Space n) R 0 := by
    intro p hp
    refine ⟨(Metric.closedBall_subset_closedBall hrR.le) hp.1,?_,hp.2.2⟩
    have ht := hp.2.1
    simp only [zero_sub] at ht ⊢
    nlinarith only [ht,hr,hrR]
  have hRegion (j : ℕ) (p : Point n) (hp : p∈autoClosed (0 : Space n) r 0) :
      ∀ q∈Metric.closedBall (0 : Space n) (eps j), p.1-q∈Metric.ball (0 : Space n) R := by
    intro q hq
    have hx : ‖p.1‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hqn : ‖q‖ ≤ eps j := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq
    have hn : ‖p.1-q‖ < R :=
      (norm_sub_le _ _).trans (add_le_add hx hqn) |>.trans_lt (hepsBuffer j)
    simpa only [Metric.mem_ball,dist_zero_right] using hn
  have hBuffer (j : ℕ) (p : Point n) (hp : p∈autoClosed (0 : Space n) r 0)
      (q : Space n) (hq : q∈Metric.closedBall (0 : Space n) (eps j)) :
      (p.1-q,p.2)∈autoClosed (0 : Space n) R 0 :=
    ⟨Metric.ball_subset_closedBall (hRegion j p hp q hq),(hSub hp).2⟩
  have hCompact : IsCompact (autoClosed (0 : Space n) R 0) := by
    exact (isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
  have hAverage := auto_spatial_average_uniform hSub H hH
    (hCompact.uniformContinuousOn_of_continuous hHC) hHBound eps heps hepszero hBuffer
  have hAll (j : ℕ) (p : Point n) (hp : p∈autoClosed (0 : Space n) r 0) :
      fderiv ℝ (fderiv ℝ (fun y => autoSpatialMollify (eps j) (heps j) w (y,p.2))) p.1=
        ∫ q, H (p.1-q,p.2) ∂autoMollifierMeasure n (eps j) (heps j) := by
    have hOpenSub : Metric.ball (0 : Space n) R ×ˢ Icc (-R^2) 0 ⊆
        autoClosed (0 : Space n) R 0 :=
      fun z hz => ⟨Metric.ball_subset_closedBall hz.1,by simpa only [zero_sub] using hz.2⟩
    apply auto_spatial_mollify_hessian_operator measurableSet_ball
      (by nlinarith only [sq_pos_of_pos hR] : -R^2 < 0)
      (heps j) w hw H hH (hHC.mono hOpenSub) hSym p.1 (hRegion j p hp)
      steps hpos hzero hB
      (fun e he k z hz => hBound e he k z (by simpa only [autoOpen,zero_sub] using hz))
      (fun e he => by simpa only [autoOpen,zero_sub] using hLimit e he)
      (fun z hz => hHBound z (hOpenSub hz)) p.2
    simpa only [autoClosed,zero_sub] using (hSub hp).2
  exact hAverage.2.congr (Eventually.of_forall fun j p hp => (hAll j p hp).symm)

end Yau.LeafProofs.L05AutonomousAux
