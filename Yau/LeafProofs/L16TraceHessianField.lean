import Yau.LeafProofs.L16TraceSpatialHessian

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceHessianField_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianField_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianField_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceHessianField_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The genuine full spatial Hessian integral equals the explicit closed
    half-space field at positive height; its normal entry is the actual
    parabolic Poisson average. -/
theorem traceSpatialHessianKernel_integral {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0)
    (e x : Space n) (hx : 0 < inner ℝ e x) :
    IntervalIntegrable (traceSpatialHessianKernel e B t x) volume 0 t ∧
      (∫ r in (0 : ℝ)..t, traceSpatialHessianKernel e B t x r) = boundaryTraceHessian e B (x,t) := by
  let P := halfSpaceBoundaryProjection e
  let a := inner ℝ e x
  let ξ := P x
  let R := (innerSL ℝ e).smulRight (innerSL ℝ e)
  let LT := traceHessianPullback P
  let LM := (traceNormalTensorMap e).comp (traceGradientPullback P)
  let LF := (ContinuousLinearMap.flipₗᵢ ℝ (Space n) (Space n) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let f : ℝ → Space n →L[ℝ] Space n →L[ℝ] ℝ := fun r => normalHeatProfile r a •
    fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ
  let m : ℝ → Space n →L[ℝ] ℝ := fun r => (2*normalGaussianKernel r a) •
    fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ
  let g : ℝ → ℝ := fun r => normalPoissonKernel a r*heatAverage r (fun y => B (y,t-r)) ξ
  have hf : IntervalIntegrable f volume 0 t := normalTraceTangentialSecond_integrable hα hB hF hH0 hH ht hx.le ξ
  have hm : IntervalIntegrable m volume 0 t := normalTraceMixed_integrable hα hB hF hH0 hH ht a ξ
  have hg : IntervalIntegrable g volume 0 t := (normalTraceFirst_hasDerivAt hB hF ht hx ξ).1
  have hTL : IntervalIntegrable (fun r => LT (f r)) volume 0 t :=
    ⟨LT.integrable_comp hf.1,LT.integrable_comp hf.2⟩
  have hML : IntervalIntegrable (fun r => LM (m r)) volume 0 t :=
    ⟨LM.integrable_comp hm.1,LM.integrable_comp hm.2⟩
  have hFL : IntervalIntegrable (fun r => LF (LM (m r))) volume 0 t :=
    ⟨LF.integrable_comp hML.1,LF.integrable_comp hML.2⟩
  have hNL : IntervalIntegrable (fun r => g r • R) volume 0 t :=
    ⟨hg.1.smul_const R,hg.2.smul_const R⟩
  have hFun : traceSpatialHessianKernel e B t x = fun r => LT (f r)+LM (m r)+LF (LM (m r))-g r • R := by
    funext r
    simp only [traceSpatialHessianKernel,LT,LM,LF,f,m,g,P,a,ξ,R,
      ContinuousLinearMap.comp_apply,map_smul]
    rfl
  rw [hFun]
  refine ⟨((hTL.add hML).add hFL).sub hNL,?_⟩
  rw [intervalIntegral.integral_sub ((hTL.add hML).add hFL) hNL,
    intervalIntegral.integral_add (hTL.add hML) hFL,intervalIntegral.integral_add hTL hML,
    LT.intervalIntegral_comp_comm hf,LM.intervalIntegral_comp_comm hm,
    LF.intervalIntegral_comp_comm hML,LM.intervalIntegral_comp_comm hm,
    intervalIntegral.integral_smul_const]
  have hgEq : (∫ r in (0 : ℝ)..t, g r) = tracePoissonAverage a B (ξ,t) :=
    finite_tracePoisson_eq_average hx ht hPast ξ
  rw [hgEq]
  rfl

/-- The explicit physical Hessian is an actual derivative of the physical
    gradient on the strict half space, including the zero initial slice. -/
theorem boundaryTraceGradient_hasFDerivAt_hessian {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0)
    {x : Space n} (hx : 0 < inner ℝ e x) :
    HasFDerivAt (fun z => boundaryTraceGradient e B (z,t)) (boundaryTraceHessian e B (x,t)) x := by
  rcases ht.eq_or_lt with rfl | ht
  · have hG : (fun z => boundaryTraceGradient e B (z,0)) = fun _ : Space n => (0 : Space n →L[ℝ] ℝ) := by
      funext z
      simp [boundaryTraceGradient,normalTraceTangential_initial,normalTraceFirst]
    have hP : tracePoissonAverage (inner ℝ e x) B (halfSpaceBoundaryProjection e x,0) = 0 := by
      rw [← finite_tracePoisson_eq_average hx le_rfl hPast (halfSpaceBoundaryProjection e x),
        intervalIntegral.integral_same]
    have hHess : boundaryTraceHessian e B (x,0) = 0 := by
      simp [boundaryTraceHessian,normalTraceTangentialSecond_initial,normalTraceMixed_initial,hP]
    rw [hG,hHess]
    exact hasFDerivAt_const 0 x
  · have h := (boundaryTraceGradient_hasFDerivAt hα he hB hF hH0 hH ht hx).2
    rwa [(traceSpatialHessianKernel_integral hα hB hF hH0 hH ht.le hPast e x hx).2] at h

end Yau.LeafProofs.L16Aux
