import Yau.LeafProofs.L05AutonomousMollifierSpace

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- On any actual source buffer, the globally smooth construction agrees with the original local average. -/
theorem autoSpatialMollify_original_average {n : ℕ} {K S : Set (Point n)}
    {u : Point n → ℝ} (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (hwu : EqOn w u K) (eps : ℝ) (heps : 0< eps)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) eps, ∀ p∈S, p+(y,0)∈K) :
    (∀ p∈S, Integrable (fun y => u (p.1+y,p.2)) (autoMollifierMeasure n eps heps)) ∧
      EqOn (autoSpatialMollify eps heps w)
        (fun p => ∫ y, u (p.1+y,p.2) ∂autoMollifierMeasure n eps heps) S := by
  let : IsProbabilityMeasure (autoMollifierMeasure n eps heps) := autoMollifierMeasure_isProbability n eps heps
  have heq (p : Point n) (hp : p∈S) :
      (fun y => w (p.1+y,p.2)) =ᵐ[autoMollifierMeasure n eps heps] (fun y => u (p.1+y,p.2)) := by
    filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with y hy
    have hh := hwu (hbuffer y hy p hp)
    have hpoint : p+(y,0)=(p.1+y,p.2) := by
      rcases p with ⟨x,t⟩
      simp only [Prod.mk_add_mk,add_zero]
    rw [hpoint] at hh
    exact hh
  constructor
  · intro p hp
    have hc : Continuous (fun y : Space n => w (p.1+y,p.2)) :=
      w.continuous.comp ((continuous_const.add continuous_id).prodMk continuous_const)
    have hi : Integrable (fun y => w (p.1+y,p.2)) (autoMollifierMeasure n eps heps) :=
      Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖w‖
        (ae_of_all _ fun y => w.norm_coe_le_norm (p.1+y,p.2))
    exact hi.congr (heq p hp)
  · intro p hp
    change autoSpatialMollify eps heps w (p.1,p.2)=_
    rw [autoSpatialMollify_integral_plus eps heps w hw]
    exact integral_congr_ae (heq p hp)

/-- The nonlinear viscosity assertion is transported only on the true original open buffer. -/
theorem autoSpatialMollify_subsolution {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {ell L : ℝ} {F : Sym n → ℝ} (hell : 0≤ ell) (hL : ell≤ L) (hF : Continuous F)
    (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsub : viscositySub (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (hwu : EqOn w u (unitClosed n))
    (eps : ℝ) (heps : 0< eps)
    (hbuffer : ∀ y∈Metric.closedBall (0 : Space n) eps, ∀ p∈Q, p+(y,0)∈unitOpen n) :
    viscositySub Q (fun H _ => F H) (fun _ => 0) (autoSpatialMollify eps heps w) := by
  let : IsProbabilityMeasure (autoMollifierMeasure n eps heps) := autoMollifierMeasure_isProbability n eps heps
  have havg := auto_probability_spatial_average_sub hQ hell hL hF hE hC hu hsub
    (Metric.closedBall (0 : Space n) eps) (isCompact_closedBall _ _) (autoMollifierMeasure n eps heps)
      (autoMollifierMeasure_closedBall_ae n eps heps) hbuffer
  have heq := (autoSpatialMollify_original_average w hw hwu eps heps
    (fun y hy p hp => unitOpen_subset_unitClosed (hbuffer y hy p hp))).2
  exact viscositySub_eqOn_open hQ heq havg.2

theorem auto_mollifier_closed_buffer {n : ℕ} {r eps : ℝ} (hr : 0< r) (heps : 0< eps)
    (hbuf : r+eps< 1) :
    ∀ y∈Metric.closedBall (0 : Space n) eps, ∀ p∈autoClosed (0 : Space n) r 0,
      p+(y,0)∈unitClosed n := by
  have hr1 : r< 1 := by linarith only [heps,hbuf]
  intro y hy p hp
  have hpy : ‖p.1+y‖< 1 := by
    have hx : ‖p.1‖≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1
    have hy' : ‖y‖≤ eps := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (add_le_add hx hy') |>.trans_lt hbuf
  have ht : -r^2≤ p.2 ∧ p.2≤ 0 := by simpa only [zero_sub,mem_Icc,mem_Ioo] using hp.2
  change p.1+y∈Metric.closedBall (0 : Space n) 1 ∧ p.2+0∈Icc (-1 : ℝ) 0
  simp only [add_zero,Metric.mem_closedBall,dist_zero_right,mem_Icc]
  refine ⟨hpy.le,?_,ht.2⟩
  nlinarith only [hr,hr1,ht.1]

theorem auto_mollifier_open_buffer {n : ℕ} {r eps : ℝ} (hr : 0< r) (heps : 0< eps)
    (hbuf : r+eps< 1) :
    ∀ y∈Metric.closedBall (0 : Space n) eps, ∀ p∈autoOpen (0 : Space n) r 0,
      p+(y,0)∈unitOpen n := by
  have hr1 : r< 1 := by linarith only [heps,hbuf]
  intro y hy p hp
  have hpy : ‖p.1+y‖< 1 := by
    have hx : ‖p.1‖< r := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
    have hy' : ‖y‖≤ eps := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (add_le_add hx.le hy') |>.trans_lt hbuf
  have ht : -r^2< p.2 ∧ p.2< 0 := by simpa only [zero_sub,mem_Icc,mem_Ioo] using hp.2
  change p.1+y∈Metric.ball (0 : Space n) 1 ∧ p.2+0∈Ioo (-1 : ℝ) 0
  simp only [add_zero,Metric.mem_ball,dist_zero_right,mem_Ioo]
  refine ⟨hpy,?_,ht.2⟩
  nlinarith only [hr,hr1,ht.1]

/-- The actual spatial smoothing converges uniformly to the unextended local data, including top time. -/
theorem autoSpatialMollify_uniform_original {n : ℕ} {S : Set (Point n)} {u : Point n → ℝ}
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (hwu : EqOn w u S)
    (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j) (hlim : Tendsto eps atTop (𝓝 0)) :
    TendstoUniformlyOn (fun j => autoSpatialMollify (eps j) (heps j) w) u atTop S := by
  have hm := Metric.tendstoUniformly_iff.mp (autoSpatialMollify_uniform w hw eps heps hlim)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  filter_upwards [hm eta heta] with j hj p hp
  rw [← hwu hp]
  exact hj p

end Yau.LeafProofs.L05AutonomousAux
