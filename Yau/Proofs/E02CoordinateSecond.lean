import Yau.Proofs.E02AffinePullback

open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

theorem continuousLinearEquiv_second_fderiv_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => f (e.symm q))) (e x) (e v) (e w) =
      fderiv ℝ (fderiv ℝ f) x v w := by
  have hAt : ContDiffAt ℝ 2 f (0+e.symm (e x)) := by
    simpa only [zero_add,ContinuousLinearEquiv.symm_apply_apply] using hf
  have h := affinePullback_second_fderiv (0 : E) e.symm.toContinuousLinearMap hAt
  have hVal := congrArg (fun A : F →L[ℝ] F →L[ℝ] ℝ => A (e v) (e w)) h
  simpa only [zero_add,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hVal

end Yau.NodeProofs.E02Aux
