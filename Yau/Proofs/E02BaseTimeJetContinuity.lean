import Yau.Proofs.E02BaseLeviQuadratic

open Matrix Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem baseTime_leviC_realTensor {n : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (z : ComplexVector n) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (z,t)) :
    leviC (fun w => f (w,t)) z =
      realTensorLevi (fderiv ℝ (fderiv ℝ f) (z,t))
        (fun i => (stdVec i,(0:ℝ))) (fun i => (Complex.I • stdVec i,(0:ℝ))) := by
  let L : ComplexVector n →L[ℝ] (ComplexVector n × ℝ) :=
    (ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0
  have hArg (w : ComplexVector n) : (0,t)+L w = (w,t) := by simp [L]
  have hAt : ContDiffAt ℝ 2 f ((0,t)+L z) := by rw [hArg]; exact hf
  have h := leviMatrix_real_affine (0,t) L hAt stdVec
  have hFun : (fun w => f ((0,t)+L w)) = (fun w => f (w,t)) := by
    funext w
    rw [hArg]
  rw [hFun,hArg] at h
  simpa only [leviC,L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] using h

/-- The original ordinary physical-time derivative is continuous at a
finite C² germ; no common C∞ neighborhood is extracted. -/
theorem continuousAt_baseTime_time_deriv {n : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (a : ComplexVector n × ℝ)
    (hf : ContDiffAt ℝ 2 f a) :
    ContinuousAt (fun p : ComplexVector n × ℝ => deriv (fun t => f (p.1,t)) p.2) a := by
  have hDf : ContinuousAt (fderiv ℝ f) a :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hEval : ContinuousAt (fun p => fderiv ℝ f p (0,1)) a :=
    hDf.clm_apply continuousAt_const
  have hNear : (fun p : ComplexVector n × ℝ => deriv (fun t => f (p.1,t)) p.2) =ᶠ[𝓝 a]
      (fun p => fderiv ℝ f p (0,1)) := by
    filter_upwards [hf.eventually (by norm_num)] with p hp
    have hLine : HasDerivAt (fun t : ℝ => (p.1,t)) (0,1) p.2 := by
      simpa using (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact ((hp.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.2 hLine).deriv
  exact hEval.congr_of_eventuallyEq hNear

/-- Continuity of the ACTUAL spatial Levi at the same finite C² germ,
computed from its genuine second Frechet derivative. -/
theorem continuousAt_baseTime_leviC {n : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (a : ComplexVector n × ℝ)
    (hf : ContDiffAt ℝ 2 f a) :
    ContinuousAt (fun p : ComplexVector n × ℝ => leviC (fun z => f (z,p.2)) p.1) a := by
  have hH : ContinuousAt (fderiv ℝ (fderiv ℝ f)) a :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hEntry (v w : ComplexVector n × ℝ) :
      ContinuousAt (fun p => fderiv ℝ (fderiv ℝ f) p v w) a :=
    (hH.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hMatrix : ContinuousAt (fun p => realTensorLevi (fderiv ℝ (fderiv ℝ f) p)
      (fun i : Fin n => (stdVec i,(0:ℝ))) (fun i => (Complex.I • stdVec i,(0:ℝ)))) a := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    let R := fun p : ComplexVector n × ℝ =>
      (fderiv ℝ (fderiv ℝ f) p (stdVec j,0) (stdVec i,0)+
        fderiv ℝ (fderiv ℝ f) p (Complex.I • stdVec j,0) (Complex.I • stdVec i,0))/4
    let J := fun p : ComplexVector n × ℝ =>
      (fderiv ℝ (fderiv ℝ f) p (stdVec j,0) (Complex.I • stdVec i,0)-
        fderiv ℝ (fderiv ℝ f) p (Complex.I • stdVec j,0) (stdVec i,0))/4
    have hRe : ContinuousAt R a := ((hEntry (stdVec j,0) (stdVec i,0)).add
      (hEntry (Complex.I • stdVec j,0) (Complex.I • stdVec i,0))).div_const 4
    have hIm : ContinuousAt J a := ((hEntry (stdVec j,0) (Complex.I • stdVec i,0)).sub
      (hEntry (Complex.I • stdVec j,0) (stdVec i,0))).div_const 4
    have hFun : (fun p => realTensorLevi (fderiv ℝ (fderiv ℝ f) p)
        (fun i : Fin n => (stdVec i,(0:ℝ))) (fun i => (Complex.I • stdVec i,(0:ℝ))) i j) =
        (fun p => (R p : ℂ)+Complex.I*(J p : ℂ)) := by
      funext p
      apply Complex.ext <;> simp [realTensorLevi,R,J]
    rw [hFun]
    exact hRe.ofReal.add ((continuousAt_const (y := Complex.I)).mul hIm.ofReal)
  apply hMatrix.congr_of_eventuallyEq
  filter_upwards [hf.eventually (by norm_num)] with p hp
  exact baseTime_leviC_realTensor f p.1 p.2 hp

end Yau.NodeProofs.E02Aux
