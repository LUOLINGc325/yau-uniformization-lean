import Yau.LeafProofs.L05ABPMollifier
import Yau.LeafProofs.L05AutonomousSecondLimit
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction Convolution
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The existing actual compact joint kernel, regarded as a genuine positive probability. -/
def autoJointMollifierMeasure (n : ℕ) (eps : ℝ) : Measure (Point n) :=
  volume.withDensity (fun q => ENNReal.ofReal (scaledKernel n eps q))

theorem autoJointMollifierMeasure_isProbability {n : ℕ} {eps : ℝ} (heps : 0 < eps) :
    IsProbabilityMeasure (autoJointMollifierMeasure n eps) := by
  constructor
  change (volume.withDensity (fun q => ENNReal.ofReal (scaledKernel n eps q))) univ=1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((scaledKernel_smooth n eps).continuous.integrable_of_hasCompactSupport (scaledKernel_compactSupport heps))
      (ae_of_all volume (scaledKernel_nonneg heps)),scaledKernel_integral heps,ENNReal.ofReal_one]

theorem autoJointMollifierMeasure_ball_ae {n : ℕ} {eps : ℝ} (heps : 0 < eps) :
    ∀ᵐ q ∂autoJointMollifierMeasure n eps, q∈Metric.ball (0 : Point n) eps := by
  change ∀ᵐ q ∂volume.withDensity (fun q => ENNReal.ofReal (scaledKernel n eps q)), _
  apply (ae_withDensity_iff (scaledKernel_smooth n eps).continuous.measurable.ennreal_ofReal).mpr
  exact ae_of_all volume fun q hq => scaledKernel_support heps (by
    intro hz
    exact hq (by rw [hz,ENNReal.ofReal_zero]))

theorem autoJointMollifierMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) {eps : ℝ} (heps : 0 < eps) (f : Point n → E) :
    (∫ q, f q ∂autoJointMollifierMeasure n eps)=∫ q, scaledKernel n eps q • f q := by
  rw [autoJointMollifierMeasure,integral_withDensity_eq_integral_toReal_smul
    (scaledKernel_smooth n eps).continuous.measurable.ennreal_ofReal
    (ae_of_all volume fun q => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact ae_of_all volume fun q => by
    change (ENNReal.ofReal (scaledKernel n eps q)).toReal • f q=scaledKernel n eps q • f q
    rw [ENNReal.toReal_ofReal (scaledKernel_nonneg heps q)]

theorem autoJointMollifierMeasure_source_integrable {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (p : Point n) :
    Integrable (fun q => w (p-q)) (autoJointMollifierMeasure n eps) := by
  let : IsProbabilityMeasure (autoJointMollifierMeasure n eps) := autoJointMollifierMeasure_isProbability heps
  have hc : Continuous (fun q => w (p-q)) := w.continuous.comp (continuous_const.sub continuous_id)
  exact Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖w‖
    (ae_of_all _ fun q => w.norm_coe_le_norm _)

theorem autoJointMollifierMeasure_average {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (p : Point n) :
    abpMollify eps w p=∫ q, w (p-q) ∂autoJointMollifierMeasure n eps := by
  rw [autoJointMollifierMeasure_integral n heps]
  rfl

/-- Genuine joint smoothing commutes with every actual finite spatial second difference. -/
theorem auto_joint_mollify_second {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (w : Point n →ᵇ ℝ) (e : Space n) (h : ℝ) (p : Point n) :
    Integrable (fun q => autoSecond w e h (p-q)) (autoJointMollifierMeasure n eps) ∧
      autoSecond (abpMollify eps w) e h p=
        ∫ q, autoSecond w e h (p-q) ∂autoJointMollifierMeasure n eps := by
  let nu := autoJointMollifierMeasure n eps
  have hplus := autoJointMollifierMeasure_source_integrable heps w (p.1+h • e,p.2)
  have hminus := autoJointMollifierMeasure_source_integrable heps w (p.1-h • e,p.2)
  have hcenter := autoJointMollifierMeasure_source_integrable heps w p
  have heq : (fun q : Point n =>
      (w ((p.1+h • e,p.2)-q)+w ((p.1-h • e,p.2)-q)-2*w (p-q))/h^2)=
      (fun q => autoSecond w e h (p-q)) := by
    funext q
    have hp : p.1+h • e-q.1=p.1-q.1+h • e := by abel
    have hm : p.1-h • e-q.1=p.1-q.1-h • e := by abel
    change (w (p.1+h • e-q.1,p.2-q.2)+w (p.1-h • e-q.1,p.2-q.2)-2*w (p-q))/h^2=
      (w (p.1-q.1+h • e,p.2-q.2)+w (p.1-q.1-h • e,p.2-q.2)-2*w (p-q))/h^2
    rw [hp,hm]
  have hsum : Integrable (fun q => w ((p.1+h • e,p.2)-q)+w ((p.1-h • e,p.2)-q)) nu :=
    hplus.add hminus
  have hi := (hsum.sub (hcenter.const_mul 2)).div_const (h^2)
  change Integrable (fun q =>
    (w ((p.1+h • e,p.2)-q)+w ((p.1-h • e,p.2)-q)-2*w (p-q))/h^2) nu at hi
  rw [heq] at hi
  refine ⟨hi,?_⟩
  change (abpMollify eps w (p.1+h • e,p.2)+abpMollify eps w (p.1-h • e,p.2)-
    2*abpMollify eps w p)/h^2=_
  rw [autoJointMollifierMeasure_average heps w (p.1+h • e,p.2),
    autoJointMollifierMeasure_average heps w (p.1-h • e,p.2),
    autoJointMollifierMeasure_average heps w p,
    ← integral_add hplus hminus,← integral_const_mul,← integral_sub hsum (hcenter.const_mul 2),
    ← integral_div]
  exact congrArg (fun f : Point n → ℝ => ∫ q, f q ∂nu) heq

/-- The actual joint positive compact convolution converges uniformly to every
uniformly continuous bounded source. -/
theorem auto_joint_mollify_uniform {n : ℕ} (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ))
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j) (hzero : Tendsto eps atTop (𝓝 0)) :
    TendstoUniformly (fun j => abpMollify (eps j) w) w atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro eta heta
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuous_iff.mp hw (eta/2) (half_pos heta)
  filter_upwards [hzero.eventually (gt_mem_nhds hdelta)] with j hj p
  have hbound : dist (abpMollify (eps j) w p) (w p) ≤ eta/2 := by
    apply abpMollify_approx (heps j) (half_pos heta).le w.continuous.stronglyMeasurable.aestronglyMeasurable p
    intro y hy
    exact (hclose (hy.trans hj)).le
  simpa only [dist_comm] using hbound.trans_lt (half_lt_self heta)

end Yau.LeafProofs.L05AutonomousAux
