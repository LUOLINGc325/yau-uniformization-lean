import Yau.LeafProofs.L16TraceAmbientExtension
import Yau.LeafProofs.L16SpatialSchwarz

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceNormalInvariance_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceNormalInvariance_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceNormalInvariance_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceNormalInvariance_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- A genuine translation-invariant differentiable function has zero derivative
    in the invariant direction. -/
theorem fderiv_zero_of_normal_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (e : E)
    (hInv : ∀ (x : E) (c : ℝ), f (x+c • e) = f x) (x : E) : fderiv ℝ f x e = 0 := by
  have hLine : HasDerivAt (fun c : ℝ => x+c • e) e 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hD := (hf x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hConst : HasDerivAt (fun c : ℝ => f (x+c • e)) 0 0 := by
    simpa only [hInv] using hasDerivAt_const (0 : ℝ) (f x)
  exact hD.unique hConst

/-- Both normal slots of the actual heat Hessian vanish for a bounded continuous
    normal-invariant source. -/
theorem heatAverage_hessian_normal_zero {n : ℕ} {r F : ℝ} (hr : 0 < r)
    (e : Space n) {g : Space n → ℝ} (hg : Continuous g) (hF : ∀ x, |g x| ≤ F)
    (hInv : ∀ (x : Space n) (c : ℝ), g (x+c • e) = g x) (x v : Space n) :
    fderiv ℝ (fderiv ℝ (heatAverage r g)) x v e = 0 ∧
      fderiv ℝ (fderiv ℝ (heatAverage r g)) x e v = 0 := by
  have hD (y : Space n) : HasFDerivAt (heatAverage r g) (fderiv ℝ (heatAverage r g) y) y :=
    (heatAverage_hasFDerivAt_kernel_of_bounded hr hg hF y).differentiableAt.hasFDerivAt
  have hDD (y : Space n) : HasFDerivAt (fderiv ℝ (heatAverage r g))
      (fderiv ℝ (fderiv ℝ (heatAverage r g)) y) y :=
    (heatAverage_fderiv_hasFDerivAt_kernel_of_bounded hr hg hF y).differentiableAt.hasFDerivAt
  have hZero : (fun y => fderiv ℝ (heatAverage r g) y e) = fun _ => (0 : ℝ) :=
    funext fun y => fderiv_zero_of_normal_invariant (fun z => (hD z).differentiableAt) e
      (heatAverage_normal_invariant g hInv r) y
  have hRight : fderiv ℝ (fderiv ℝ (heatAverage r g)) x v e = 0 := by
    rw [← fderiv_clm_const_eval (hDD x).differentiableAt e v,hZero]
    simp only [fderiv_fun_const,Pi.zero_apply,zero_apply]
  exact ⟨hRight,(second_derivative_symmetric hD (hDD x) e v).trans hRight⟩

/-- Pulling a bilinear form back by the boundary projection leaves it unchanged
    when both of its genuine normal slots vanish. -/
theorem traceHessianPullback_eq_of_normal_zero {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (A : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (hR : ∀ v, A v e = 0) (hL : ∀ v, A e v = 0) :
    traceHessianPullback (halfSpaceBoundaryProjection e) A = A := by
  ext v w
  simp only [traceHessianPullback_apply,halfSpaceBoundaryProjection_apply he,
    map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,
    hR,hL,mul_zero,sub_zero]

/-- The actual integrated tangential Hessian is unaffected by the physical
    boundary projection for a normal-invariant source. -/
theorem normalTraceTangentialSecond_pullback {n : ℕ} {α F t a : ℝ}
    (hα : 0 < α) {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α)
    (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hInv : ∀ (x : Space n) (c s : ℝ), B (x+c • e,s) = B (x,s)) (ξ : Space n) :
    traceHessianPullback (halfSpaceBoundaryProjection e) (normalTraceTangentialSecond B t a ξ) =
      normalTraceTangentialSecond B t a ξ := by
  let L := traceHessianPullback (halfSpaceBoundaryProjection e)
  have hF0 : 0 ≤ F := (abs_nonneg (B (0,0))).trans (hF (0,0))
  have hi := normalTraceTangentialSecond_integrable hα hB hF hF0 hH ht ha ξ
  change L (∫ r in (0 : ℝ)..t, normalHeatProfile r a •
      fderiv ℝ (fderiv ℝ (heatAverage r (fun y => B (y,t-r)))) ξ) = _
  rw [← L.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all
  intro r hr
  have hr' : 0 < r := (show r ∈ Ioc 0 t from by simpa only [uIoc_of_le ht] using hr).1
  rw [map_smul]
  have hN := heatAverage_hessian_normal_zero hr' e
    (hB.comp (continuous_id.prodMk continuous_const)) (fun y => hF (y,t-r))
    (fun x c => hInv x c (t-r)) ξ
  congr 1
  exact traceHessianPullback_eq_of_normal_zero he _ (fun v => (hN v).1) (fun v => (hN v).2)

/-- The trace of a real normal tensor is its genuine contraction with the normal. -/
theorem heatTrace_normal_tensor {n : ℕ} (e : Space n) (A : Space n →L[ℝ] ℝ) :
    heatTrace (traceNormalTensorMap e A) = A e := by
  have hRepr : (∑ i : Yau.RIdx n, (inner ℝ e (Yau.realVec i)) • Yau.realVec i) = e := by
    simpa only [spaceRealBasis_apply,real_inner_comm] using (spaceRealBasis n).sum_repr' e
  calc
    _ = ∑ i : Yau.RIdx n, inner ℝ e (Yau.realVec i)*A (Yau.realVec i) := by
      simp only [heatTrace_apply,traceNormalTensorMap_apply,ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply,smul_apply,smul_eq_mul]
    _ = A (∑ i : Yau.RIdx n, inner ℝ e (Yau.realVec i) • Yau.realVec i) := by
      simp only [map_sum,map_smul,smul_eq_mul]
    _ = _ := by rw [hRepr]

/-- The trace of the unit normal square is exactly one. -/
theorem heatTrace_normal_square {n : ℕ} {e : Space n} (he : ‖e‖ = 1) :
    heatTrace ((innerSL ℝ e).smulRight (innerSL ℝ e)) = 1 := by
  change heatTrace (traceNormalTensorMap e (innerSL ℝ e)) = 1
  rw [heatTrace_normal_tensor,innerSL_apply_apply,real_inner_self_eq_norm_sq,he,one_pow]

/-- Taking the real heat trace is unchanged by flipping a bilinear form. -/
theorem heatTrace_flip {n : ℕ} (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    heatTrace A.flip = heatTrace A := by
  simp only [heatTrace_apply,ContinuousLinearMap.flip_apply]

/-- The trace of the complete physical Hessian equals its tangential trace
    minus the actual Poisson normal jet; both mixed contractions vanish. -/
theorem boundaryTraceHessian_trace {n : ℕ} {α F t : ℝ}
    (hα : 0 < α) {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : HolderBound α univ B F) (ht : 0 ≤ t)
    (hInv : ∀ (x : Space n) (c s : ℝ), B (x+c • e,s) = B (x,s))
    (x : Space n) (hx : 0 ≤ inner ℝ e x) :
    heatTrace (boundaryTraceHessian e B (x,t)) =
      heatTrace (normalTraceTangentialSecond B t (inner ℝ e x) (halfSpaceBoundaryProjection e x))-
        tracePoissonAverage (inner ℝ e x) B (halfSpaceBoundaryProjection e x,t) := by
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s y z, |B (y,s)-B (z,s)| ≤ F*‖y-z‖^α := by
    intro s y z
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (y,s) (mem_univ _) (z,s) (mem_univ _)
  have hPe : halfSpaceBoundaryProjection e e = 0 := by
    rw [halfSpaceBoundaryProjection_apply he,real_inner_self_eq_norm_sq,he,one_pow,one_smul,sub_self]
  let M := traceGradientPullback (halfSpaceBoundaryProjection e)
    (normalTraceMixed B t (inner ℝ e x) (halfSpaceBoundaryProjection e x))
  have hMe : M e = 0 := by simp only [M,traceGradientPullback_apply,ContinuousLinearMap.comp_apply,hPe,map_zero]
  change heatTrace (traceHessianPullback (halfSpaceBoundaryProjection e)
      (normalTraceTangentialSecond B t (inner ℝ e x) (halfSpaceBoundaryProjection e x))+
      traceNormalTensorMap e M+(traceNormalTensorMap e M).flip-
      tracePoissonAverage (inner ℝ e x) B (halfSpaceBoundaryProjection e x,t) •
        (innerSL ℝ e).smulRight (innerSL ℝ e)) = _
  rw [map_sub,map_add,map_add,map_smul,heatTrace_flip,heatTrace_normal_tensor,hMe,
    heatTrace_normal_square he,normalTraceTangentialSecond_pullback hα he hc hb hh ht hx hInv]
  simp only [add_zero,smul_eq_mul,mul_one]

/-- The extended layer satisfies the literal Euclidean heat equation on the
    whole closed half space, for its normal-invariant boundary source. -/
theorem boundaryTraceLayer_extension_linearOp {n : ℕ} {α F T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : HolderBound α univ B F) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0)
    (hInv : ∀ (x : Space n) (c s : ℝ), B (x+c • e,s) = B (x,s))
    {p : Point n} (hp : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T) :
    linearOp (cylinder univ 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0)
      (halfSpaceSecondOrderExtension e (boundaryTraceLayer e B)) p = B p := by
  have hJets := boundaryTraceLayer_extension_jets hα hα1 hT hT1 he hB hPast
  have hTrace := boundaryTraceHessian_trace hα he hB hp.2.1 hInv p.1 hp.1
  have hSource : B (halfSpaceBoundaryProjection e p.1,p.2) = B p := by
    rw [halfSpaceBoundaryProjection_apply he]
    simpa only [neg_smul,sub_eq_add_neg] using hInv p.1 (-inner ℝ e p.1) p.2
  unfold linearOp
  rw [hJets.2.2.2.2 hp]
  have hHessian := hJets.2.2.2.1 hp
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  have hIdentity (A : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, (1 : Mat n) i j*A (Yau.realVec i) (Yau.realVec j)) =
        heatTrace A := by simp [Matrix.one_apply,heatTrace_apply]
  rw [hIdentity]
  rw [hHessian]
  change B (halfSpaceBoundaryProjection e p.1,p.2)+
    heatTrace (normalTraceTangentialSecond B p.2 (inner ℝ e p.1) (halfSpaceBoundaryProjection e p.1))-
    tracePoissonAverage (inner ℝ e p.1) B (halfSpaceBoundaryProjection e p.1,p.2)-
    heatTrace (boundaryTraceHessian e B p) = B p
  rw [hSource,hTrace]
  ring

end Yau.LeafProofs.L16Aux
