import spec.CHAIN.CONTRACTS

/-! A fixed continuous linear currying map turns the actual spatial
second Taylor jet into its native nested real Hessian. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def secondSpatialJetCurryingCLM :
    (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) →L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
  let C : (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) →L[ℝ] (E →L[ℝ] F) :=
    (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  let L : (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) →L[ℝ]
      (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).toContinuousLinearEquiv.toContinuousLinearMap
  ((ContinuousLinearMap.compL ℝ E
    (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) F) (E →L[ℝ] F)) C).comp L

theorem secondSpatialJetCurryingCLM_native (f : E → F) (x : E) :
    secondSpatialJetCurryingCLM (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change iteratedFDeriv ℝ 2 f x (Fin.cons v (Fin.snoc 0 w)) = fderiv ℝ (fderiv ℝ f) x v w
  rw [iteratedFDeriv_two_apply]
  rfl

end Yau.NodeProofs.F01Aux
