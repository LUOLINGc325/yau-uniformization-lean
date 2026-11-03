import Yau.Proofs.C02ConnectionCurvature

/-! Curvature of a pulled-back connection is the pullback of the computed
curvature. The second derivatives of the actual base map cancel. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance pullback_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance pullback_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance pullback_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance pullback_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def pullbackConnection (Γ : E → E →L[ℝ] E →L[ℝ] E) (f : E → E) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  (Γ (f x)).comp (fderiv ℝ f x)

theorem connectionCurvature_pullback (Γ : E → E →L[ℝ] E →L[ℝ] E) (f : E → E)
    (x u v : E) (hΓ : DifferentiableAt ℝ Γ (f x)) (hf : ContDiffAt ℝ 2 f x) :
    connectionCurvature (pullbackConnection Γ f) x u v =
      connectionCurvature Γ (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) := by
  have hfD := hf.differentiableAt (by norm_num)
  have hfDD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hG : HasFDerivAt (fun y => Γ (f y))
      ((fderiv ℝ Γ (f x)).comp (fderiv ℝ f x)) x :=
    hΓ.hasFDerivAt.comp x hfD.hasFDerivAt
  have hD := hG.clm_comp hfDD.hasFDerivAt
  have hVal (a b : E) : fderiv ℝ (pullbackConnection Γ f) x a b =
      Γ (f x) (fderiv ℝ (fderiv ℝ f) x a b) +
        fderiv ℝ Γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
    change fderiv ℝ (fun y => (Γ (f y)).comp (fderiv ℝ f y)) x a b = _
    have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] E →L[ℝ] E => L a b) hD.fderiv
    simpa only [pullbackConnection, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] using he
  have hSymm := hf.isSymmSndFDerivAt (by norm_num) u v
  rw [connectionCurvature_apply, connectionCurvature_apply, hVal, hVal, hSymm]
  simp only [pullbackConnection, ContinuousLinearMap.comp_apply]
  abel

end Yau.Blueprint.C02Proof
