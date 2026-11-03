import Yau.LeafProofs.L05AutonomousMollifierKernel

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction Convolution
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoTimeSliceBCF {n : ℕ} (w : Point n →ᵇ ℝ) (x : Space n) : ℝ →ᵇ ℝ :=
  w.compContinuous ⟨fun t => (x,t),continuous_const.prodMk continuous_id⟩

theorem autoTimeSliceBCF_apply {n : ℕ} (w : Point n →ᵇ ℝ) (x : Space n) (t : ℝ) :
    autoTimeSliceBCF w x t=w (x,t) := rfl

theorem autoTimeSliceBCF_norm {n : ℕ} (w : Point n →ᵇ ℝ) (x : Space n) :
    ‖autoTimeSliceBCF w x‖≤ ‖w‖ := BoundedContinuousFunction.norm_compContinuous_le _ _

/-- The actual time-function-valued source is continuous in the supremum norm. -/
theorem autoTimeSliceBCF_uniformContinuous {n : ℕ} (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) : UniformContinuous (autoTimeSliceBCF w) := by
  let path : ContinuousMap ℝ (Point n) := ⟨fun t => (0,t),continuous_const.prodMk continuous_id⟩
  have heq : autoTimeSliceBCF w=(fun x => (autoSpatialTranslateBCF w x).compContinuous path) := by
    funext x
    ext t
    change w (x,t)=w (((0 : Space n),t)+(x,0))
    simp only [Prod.mk_add_mk,zero_add,add_zero]
  rw [heq]
  exact (BoundedContinuousFunction.lipschitz_compContinuous path).uniformContinuous.comp
    (autoSpatialTranslateBCF_uniformContinuous w hw)

/-- This is a genuine Banach-valued spatial convolution; time remains a parameter. -/
def autoSpatialMollifyBCF {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ) :
    Space n → ℝ →ᵇ ℝ :=
  autoMollifierKernel n eps heps ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] autoTimeSliceBCF w

def autoSpatialMollify {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ) (p : Point n) : ℝ :=
  autoSpatialMollifyBCF eps heps w p.1 p.2

theorem autoSpatialMollifyBCF_contDiff {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) : ContDiff ℝ ∞ (autoSpatialMollifyBCF eps heps w) := by
  have hg : LocallyIntegrable (autoTimeSliceBCF w) (volume : Measure (Space n)) :=
    (autoTimeSliceBCF_uniformContinuous w hw).continuous.locallyIntegrable
  exact (autoMollifierKernel_compact n eps heps).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (autoMollifierKernel_contDiff n eps heps) hg

theorem autoSpatialMollify_continuous {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) : Continuous (autoSpatialMollify eps heps w) :=
  ((autoSpatialMollifyBCF_contDiff eps heps w hw).continuous.comp continuous_fst).eval continuous_snd

/-- Evaluation at a fixed time is a continuous linear map, so these are actual spatial derivatives. -/
theorem autoSpatialMollify_spatial_contDiff {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => autoSpatialMollify eps heps w (x,t)) := by
  let ev : (ℝ →ᵇ ℝ) →L[ℝ] ℝ := BoundedContinuousFunction.evalCLM ℝ t
  have hh := ev.contDiff.comp (autoSpatialMollifyBCF_contDiff eps heps w hw)
  simpa only [ev,autoSpatialMollify,Function.comp_def,BoundedContinuousFunction.evalCLM_apply] using hh

theorem auto_bcf_slice_second {n : ℕ} {g : Space n → ℝ →ᵇ ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Space n) (t : ℝ) (i j : Yau.RIdx n) :
    (fderiv ℝ (fderiv ℝ (fun y => g y t)) x) (Yau.realVec i) (Yau.realVec j)=
      (fderiv ℝ (fderiv ℝ g) x (Yau.realVec i) (Yau.realVec j)) t := by
  have hh := (BoundedContinuousFunction.evalCLM ℝ t).iteratedFDeriv_comp_left (x := x) hg.contDiffAt (i := 2) (by simp)
  have hval := congrArg (fun A => A ![Yau.realVec i,Yau.realVec j]) hh
  simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,Function.comp_def,
    iteratedFDeriv_two_apply,BoundedContinuousFunction.evalCLM_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using hval

/-- Each genuine Hessian entry is jointly continuous in space and time. -/
theorem autoSpatialMollify_second_continuous {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (i j : Yau.RIdx n) :
    Continuous (fun p : Point n =>
      (fderiv ℝ (fderiv ℝ (fun x => autoSpatialMollify eps heps w (x,p.2))) p.1)
        (Yau.realVec i) (Yau.realVec j)) := by
  have hm := autoSpatialMollifyBCF_contDiff eps heps w hw
  have hc : Continuous (fun x : Space n =>
      fderiv ℝ (fderiv ℝ (autoSpatialMollifyBCF eps heps w)) x (Yau.realVec i) (Yau.realVec j)) :=
    ((((hm.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).clm_apply
      contDiff_const).continuous
  have hactual := (hc.comp continuous_fst).eval continuous_snd
  have heq : (fun p : Point n =>
      (fderiv ℝ (fderiv ℝ (fun x => autoSpatialMollify eps heps w (x,p.2))) p.1)
        (Yau.realVec i) (Yau.realVec j))=
      (fun p : Point n => (fderiv ℝ (fderiv ℝ (autoSpatialMollifyBCF eps heps w)) p.1
        (Yau.realVec i) (Yau.realVec j)) p.2) := by
    funext p
    exact auto_bcf_slice_second hm p.1 p.2 i j
  rwa [heq]

theorem autoMollifierMeasure_integral_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (eps : ℝ) (heps : 0< eps) (f : Space n → E) :
    (∫ x, f (-x) ∂autoMollifierMeasure n eps heps)=∫ x, f x ∂autoMollifierMeasure n eps heps := by
  rw [autoMollifierMeasure_integral,autoMollifierMeasure_integral]
  have hh := integral_neg_eq_self (fun x : Space n => autoMollifierKernel n eps heps x • f x) volume
  change (∫ x, autoMollifierKernel n eps heps (-x) • f (-x))=∫ x, autoMollifierKernel n eps heps x • f x at hh
  simpa only [autoMollifierKernel_even] using hh

theorem autoSpatialMollifyBCF_integrable {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (x : Space n) :
    Integrable (fun y => autoTimeSliceBCF w (x-y)) (autoMollifierMeasure n eps heps) := by
  let : IsProbabilityMeasure (autoMollifierMeasure n eps heps) := autoMollifierMeasure_isProbability n eps heps
  have hc : Continuous (fun y => autoTimeSliceBCF w (x-y)) :=
    (autoTimeSliceBCF_uniformContinuous w hw).continuous.comp (continuous_const.sub continuous_id)
  exact Integrable.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖w‖
    (ae_of_all _ fun y => autoTimeSliceBCF_norm w (x-y))

theorem autoSpatialMollifyBCF_integral {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ) (x : Space n) :
    autoSpatialMollifyBCF eps heps w x=
      ∫ y, autoTimeSliceBCF w (x-y) ∂autoMollifierMeasure n eps heps := by
  rw [autoMollifierMeasure_integral]
  rfl

/-- The smooth Banach-valued construction is exactly the literal scalar spatial average. -/
theorem autoSpatialMollify_integral_minus {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (x : Space n) (t : ℝ) :
    autoSpatialMollify eps heps w (x,t)=∫ y, w (x-y,t) ∂autoMollifierMeasure n eps heps := by
  change autoSpatialMollifyBCF eps heps w x t=_
  rw [autoSpatialMollifyBCF_integral]
  have hh := (BoundedContinuousFunction.evalCLM ℝ t).integral_comp_comm
    (autoSpatialMollifyBCF_integrable eps heps w hw x)
  simpa only [BoundedContinuousFunction.evalCLM_apply,autoTimeSliceBCF_apply,Function.comp_def] using hh.symm

theorem autoSpatialMollify_integral_plus {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (x : Space n) (t : ℝ) :
    autoSpatialMollify eps heps w (x,t)=∫ y, w (x+y,t) ∂autoMollifierMeasure n eps heps := by
  rw [autoSpatialMollify_integral_minus eps heps w hw]
  have hh := autoMollifierMeasure_integral_neg n eps heps (fun y => w (x-y,t))
  simp only [sub_neg_eq_add] at hh
  exact hh.symm

/-- The mollification retains the original actual sup budget uniformly in the smoothing scale. -/
theorem autoSpatialMollify_abs_le {n : ℕ} (eps : ℝ) (heps : 0< eps) (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (p : Point n) :
    |autoSpatialMollify eps heps w p|≤ ‖w‖ := by
  let : IsProbabilityMeasure (autoMollifierMeasure n eps heps) := autoMollifierMeasure_isProbability n eps heps
  have hh := norm_integral_le_of_norm_le_const (μ := autoMollifierMeasure n eps heps)
    (f := fun y => w (p.1-y,p.2)) (ae_of_all _ fun y => w.norm_coe_le_norm (p.1-y,p.2))
  rw [autoSpatialMollify_integral_minus eps heps w hw p.1 p.2]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

/-- Uniform convergence follows from actual uniform continuity, with no quantitative modulus assumed. -/
theorem autoSpatialMollify_uniform {n : ℕ} (w : Point n →ᵇ ℝ)
    (hw : UniformContinuous (w : Point n → ℝ)) (eps : ℕ → ℝ) (heps : ∀ j, 0< eps j)
    (hlim : Tendsto eps atTop (𝓝 0)) :
    TendstoUniformly (fun j => autoSpatialMollify (eps j) (heps j) w) w atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro eta heta
  have hg := autoTimeSliceBCF_uniformContinuous w hw
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuous_iff.mp hg (eta/2) (half_pos heta)
  filter_upwards [hlim.eventually (gt_mem_nhds hdelta)] with j hj p
  have hbound : dist (autoSpatialMollifyBCF (eps j) (heps j) w p.1) (autoTimeSliceBCF w p.1)≤ eta/2 := by
    apply (autoMollifierBump n (eps j) (heps j)).dist_normed_convolution_le
      hg.continuous.stronglyMeasurable.aestronglyMeasurable
    intro y hy
    have hh : dist y p.1< eps j := hy
    exact (hclose (hh.trans hj)).le
  have hpoint : dist ((autoSpatialMollifyBCF (eps j) (heps j) w p.1) p.2)
      ((autoTimeSliceBCF w p.1) p.2)≤ eta/2 :=
    (BoundedContinuousFunction.dist_coe_le_dist p.2).trans hbound
  have hh := hpoint.trans_lt (half_lt_self heta)
  simpa only [autoSpatialMollify,autoTimeSliceBCF_apply,Prod.eta,dist_comm] using hh

end Yau.LeafProofs.L05AutonomousAux
