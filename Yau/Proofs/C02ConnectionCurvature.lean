import Yau.Proofs.C02RadialHomotopy

/-! Curvature of a linear connection field in fixed vector-space coordinates.
This is the computed derivative/commutator expression, not an input tensor. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance connection_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance connection_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance connection_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance connection_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance connection_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance connection_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

def connectionCurvature (A : E → E →L[ℝ] E →L[ℝ] E) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  let D := fderiv ℝ A x
  let P := (ContinuousLinearMap.compL ℝ E E E).bilinearComp (A x) (A x)
  D - D.flip + P - P.flip

theorem connectionCurvature_apply (A : E → E →L[ℝ] E →L[ℝ] E) (x u v : E) :
    connectionCurvature A x u v = fderiv ℝ A x u v - fderiv ℝ A x v u +
      (A x u).comp (A x v) - (A x v).comp (A x u) := rfl

theorem connectionCurvature_smooth [FiniteDimensional ℝ E]
    (A : E → E →L[ℝ] E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (connectionCurvature A) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (by simp)
  rw [← contDiffOn_univ]
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hu : ContDiff ℝ ∞ (fun _ : E => u) := contDiff_const
  have hv : ContDiff ℝ ∞ (fun _ : E => v) := contDiff_const
  have hd1 := (hD.clm_apply hu).clm_apply hv
  have hd2 := (hD.clm_apply hv).clm_apply hu
  have hp1 := (hA.clm_apply hu).clm_comp (hA.clm_apply hv)
  have hp2 := (hA.clm_apply hv).clm_comp (hA.clm_apply hu)
  simpa only [connectionCurvature_apply] using (((hd1.sub hd2).add hp1).sub hp2).contDiffOn

end Yau.Blueprint.C02Proof
