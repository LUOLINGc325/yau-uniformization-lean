import Yau.LeafProofs.L05AutonomousMollifierAverage
import Yau.LeafProofs.L05AutonomousTimeIncrementsFTC
import Yau.LeafProofs.L17SchauderSpaceIntegral

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual scalar time slice is integrable against the actual smoothing probability. -/
theorem autoSpatialMollify_time_slice_integrable {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (w : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ)) (x : Space n) (t : ℝ) :
    Integrable (fun y => w (x-y,t)) (autoMollifierMeasure n eps heps) := by
  have hh := (BoundedContinuousFunction.evalCLM ℝ t).integrable_comp
    (autoSpatialMollifyBCF_integrable eps heps w hw x)
  simpa only [BoundedContinuousFunction.evalCLM_apply,autoTimeSliceBCF_apply,Function.comp_def] using hh

/-- Interval integration is a genuine continuous linear functional on the time Banach space. -/
theorem autoSpatialMollify_interval_swap {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (v : Point n →ᵇ ℝ) (hv : UniformContinuous (v : Point n → ℝ)) (x : Space n) (a b : ℝ) :
    (∫ t in a..b, autoSpatialMollify eps heps v (x,t))=
      ∫ y, (∫ t in a..b, v (x-y,t)) ∂autoMollifierMeasure n eps heps := by
  let L : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
    Yau.LeafProofs.L17SchauderAux.pathIntegralCLM id continuous_id (ContinuousLinearMap.id ℝ ℝ) a b
  have hh : L (autoSpatialMollifyBCF eps heps v x)=
      ∫ y, L (autoTimeSliceBCF v (x-y)) ∂autoMollifierMeasure n eps heps := by
    rw [autoSpatialMollifyBCF_integral]
    exact (L.integral_comp_comm (autoSpatialMollifyBCF_integrable eps heps v hv x)).symm
  simpa only [L,Yau.LeafProofs.L17SchauderAux.pathIntegralCLM_apply,ContinuousLinearMap.id_apply,
    id_eq,autoTimeSliceBCF_apply,autoSpatialMollify] using hh

/-- Literal source FTC identities commute with the actual spatial convolution. -/
theorem autoSpatialMollify_interval_ftc {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (w v : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (hv : UniformContinuous (v : Point n → ℝ)) (x : Space n) (a b : ℝ)
    (hFTC : ∀ y∈Metric.closedBall (0 : Space n) eps,
      w (x-y,b)-w (x-y,a)=∫ t in a..b, v (x-y,t)) :
    autoSpatialMollify eps heps w (x,b)-autoSpatialMollify eps heps w (x,a)=
      ∫ t in a..b, autoSpatialMollify eps heps v (x,t) := by
  rw [autoSpatialMollify_integral_minus eps heps w hw x b,
    autoSpatialMollify_integral_minus eps heps w hw x a,
    ← integral_sub (autoSpatialMollify_time_slice_integrable eps heps w hw x b)
      (autoSpatialMollify_time_slice_integrable eps heps w hw x a),autoSpatialMollify_interval_swap eps heps v hv]
  apply integral_congr_ae
  filter_upwards [autoMollifierMeasure_closedBall_ae n eps heps] with y hy
  exact hFTC y hy

/-- The derivatives are recovered from genuine FTC, on the open interval and at both closed endpoints. -/
theorem autoSpatialMollify_time_derivatives {n : ℕ} (eps : ℝ) (heps : 0< eps)
    (w v : Point n →ᵇ ℝ) (hw : UniformContinuous (w : Point n → ℝ))
    (hv : UniformContinuous (v : Point n → ℝ)) (x : Space n) {a b : ℝ} (hab : a< b)
    (hFTC : ∀ y∈Metric.closedBall (0 : Space n) eps, ∀ s∈Icc a b, ∀ t∈Icc a b,
      w (x-y,t)-w (x-y,s)=∫ tau in s..t, v (x-y,tau)) :
    (∀ t∈Icc a b, HasDerivWithinAt (fun tau => autoSpatialMollify eps heps w (x,tau))
      (autoSpatialMollify eps heps v (x,t)) (Icc a b) t) ∧
    (∀ t∈Ioo a b, HasDerivAt (fun tau => autoSpatialMollify eps heps w (x,tau))
      (autoSpatialMollify eps heps v (x,t)) t) := by
  have hcont : Continuous (fun t => autoSpatialMollify eps heps v (x,t)) :=
    (autoSpatialMollify_continuous eps heps v hv).comp (continuous_const.prodMk continuous_id)
  have hSmFTC : ∀ s∈Icc a b, ∀ t∈Icc a b,
      autoSpatialMollify eps heps w (x,t)-autoSpatialMollify eps heps w (x,s)=
        ∫ tau in s..t, autoSpatialMollify eps heps v (x,tau) := by
    intro s hs t ht
    exact autoSpatialMollify_interval_ftc eps heps w v hw hv x s t (fun y hy => hFTC y hy s hs t ht)
  exact ⟨fun t ht => auto_hasDerivWithinAt_of_ftc hab hcont.continuousOn hSmFTC ht,
    fun t ht => auto_hasDerivAt_of_ftc hab hcont.continuousOn hSmFTC ht⟩

end Yau.LeafProofs.L05AutonomousAux
