import Yau.LeafProofs.L05AutonomousMollifierTime
import Yau.LeafProofs.L05AutonomousSliceTests
import Yau.LeafProofs.L05AutonomousSlopes

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The symmetrized actual spatial Hessian, including its top-face values, is jointly continuous. -/
theorem autoSpatialMollify_hessian_continuous {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) :
    Continuous (hessian (autoSpatialMollify eps heps w)) := by
  have hentries : Continuous (fun p : Point n => fun i j : Yau.RIdx n =>
      fderiv ℝ (fderiv ℝ (fun x => autoSpatialMollify eps heps w (x,p.2))) p.1
        (Yau.realVec i) (Yau.realVec j)) :=
    continuous_pi fun i => continuous_pi fun j => autoSpatialMollify_second_continuous eps heps w hw i j
  exact (continuous_selfAdjointPart ℝ (Mat n)).comp hentries

theorem autoSpatialMollify_trace_continuous {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (A : Sym n) :
    Continuous (fun p => tracePair A (hessian (autoSpatialMollify eps heps w) p)) := by
  have hh := (autoTraceFunctional A).continuous.comp (autoSpatialMollify_hessian_continuous eps heps w hw)
  have heq : (fun p : Point n => autoTraceFunctional A (hessian (autoSpatialMollify eps heps w) p))=
      (fun p => tracePair A (hessian (autoSpatialMollify eps heps w) p)) := by
    funext p
    rw [autoTraceFunctional_apply]
    exact Matrix.trace_mul_comm _ _
  change Continuous (fun p : Point n => autoTraceFunctional A (hessian (autoSpatialMollify eps heps w) p)) at hh
  rwa [heq] at hh

/-- True time FTC plus the native subsolution yields the supporting trace bound on the entire closed cylinder. -/
theorem autoSpatialMollify_supporting_trace_lower {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0< ell) (hL : ell≤ L) (hF : Continuous F) (hE : globalElliptic F ell L)
    (hC : ConcaveOn ℝ univ F) {u : Point n → ℝ} (hu : ContinuousOn u (unitClosed n))
    (hsub : viscositySub (unitOpen n) (fun H _ => F H) (fun _ => 0) u)
    (w v : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (hv : UniformContinuous (v : Point n → ℝ)) (hwu : EqOn w u (unitClosed n))
    {r eps : ℝ} (hr : 0< r) (heps : 0< eps) (hbuf : r+eps< 1)
    (hFTC : ∀ x∈Metric.closedBall (0 : Space n) r, ∀ y∈Metric.closedBall (0 : Space n) eps,
      ∀ a∈Icc (-r^2) 0, ∀ b∈Icc (-r^2) 0, w (x-y,b)-w (x-y,a)=∫ t in a..b, v (x-y,t))
    (A : Sym n) (hA : ∀ H, F H≤ tracePair A H) :
    ∀ p∈autoClosed (0 : Space n) r 0,
      -‖v‖≤ tracePair A (hessian (autoSpatialMollify eps heps w) p) := by
  have hQ : IsOpen (autoOpen (0 : Space n) r 0) := Metric.isOpen_ball.prod isOpen_Ioo
  have hSmoothSub := autoSpatialMollify_subsolution hQ hell.le hL hF hE hC hu hsub w hw hwu eps heps
    (auto_mollifier_open_buffer hr heps hbuf)
  have hTime (p : Point n) (hp : p∈autoOpen (0 : Space n) r 0) :
      HasDerivAt (fun t => autoSpatialMollify eps heps w (p.1,t)) (autoSpatialMollify eps heps v p) p.2 := by
    have hx : p.1∈Metric.closedBall (0 : Space n) r := Metric.ball_subset_closedBall hp.1
    have ht : p.2∈Ioo (-r^2) 0 := by simpa only [zero_sub] using hp.2
    exact (autoSpatialMollify_time_derivatives eps heps w v hw hv p.1
      (by nlinarith only [sq_pos_of_pos hr] : -r^2< 0) (hFTC p.1 hx)).2 p.2 ht
  have hOpen : ∀ p∈autoOpen (0 : Space n) r 0,
      -‖v‖≤ tracePair A (hessian (autoSpatialMollify eps heps w) p) := by
    intro p hp
    have hres := auto_actual_residual_sub hQ hF
      (autoSpatialMollify_continuous eps heps w hw).continuousOn
      (autoSpatialMollify_continuous eps heps v hv).continuousOn hTime hSmoothSub hp
      ((autoSpatialMollify_spatial_contDiff eps heps w hw p.2).of_le (by simp)).contDiffAt
    have hV := (abs_le.mp (autoSpatialMollify_abs_le eps heps v hv p)).1
    exact hV.trans (hres.trans (hA _))
  have hclosed : IsClosed {p : Point n | -‖v‖≤ tracePair A (hessian (autoSpatialMollify eps heps w) p)} :=
    isClosed_le continuous_const (autoSpatialMollify_trace_continuous eps heps w hw A)
  have hclosure : closure (autoOpen (0 : Space n) r 0)=autoClosed (0 : Space n) r 0 := by
    rw [autoOpen,autoClosed,closure_prod_eq,closure_ball (0 : Space n) hr.ne',
      closure_Ioo (by nlinarith only [sq_pos_of_pos hr] : (0 : ℝ)-r^2≠0)]
  intro p hp
  exact (hclosed.closure_subset_iff.mpr hOpen) (by rwa [hclosure])

end Yau.LeafProofs.L05AutonomousAux
