import Yau.Blueprint.Nodes

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- Postcomposition by a fixed bounded real-linear map transports the
genuine second derivative, including matrix-entry and real-trace maps. -/
theorem second_fderiv_continuousLinearMap_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) (L : F →L[ℝ] G) (v w : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) x v w = L (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hNear : fderiv ℝ (L ∘ f) =ᶠ[𝓝 x] (fun y => L.comp (fderiv ℝ f y)) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [fderiv_comp y L.differentiableAt (hy.differentiableAt (by norm_num))]
    exact congrArg (fun A : F →L[ℝ] G => A.comp (fderiv ℝ f y)) L.hasFDerivAt.fderiv
  have hD := (ContinuousLinearMap.compL ℝ E F G L).hasFDerivAt.comp x hDf.hasFDerivAt
  have hSecond := hNear.fderiv_eq (𝕜 := ℝ)
  have hPost := hD.fderiv
  change fderiv ℝ (fun y => L.comp (fderiv ℝ f y)) x =
    (ContinuousLinearMap.compL ℝ E F G L).comp (fderiv ℝ (fderiv ℝ f) x) at hPost
  rw [hPost] at hSecond
  exact congrArg (fun A : E →L[ℝ] E →L[ℝ] G => A v w) hSecond

end Yau.NodeProofs.E02Aux
