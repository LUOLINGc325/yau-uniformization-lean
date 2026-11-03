import Yau.Proofs.C02InverseFieldDerivative

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance idop_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance idop_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance idop_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance idop_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def inverseDerivativeLeft : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E).precompR E

def inverseDerivativeRight : (E →L[ℝ] E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E).precompL E

theorem inverseDerivativeLeft_norm_le_one : ‖inverseDerivativeLeft E‖ ≤ 1 :=
  ((ContinuousLinearMap.compL ℝ E E E).norm_precompR_le E).trans (ContinuousLinearMap.norm_compL_le ℝ E E E)

theorem inverseDerivativeRight_norm_le_one : ‖inverseDerivativeRight E‖ ≤ 1 :=
  ((ContinuousLinearMap.compL ℝ E E E).norm_precompL_le E).trans (ContinuousLinearMap.norm_compL_le ℝ E E E)

theorem actualInverseField_fderiv_operator [CompleteSpace E] {B : E → E →L[ℝ] E}
    (hB : ContDiff ℝ ∞ B) {x : E} (hx : (B x).IsInvertible) :
    fderiv ℝ (fun y => (B y).inverse) x =
      -inverseDerivativeRight E (inverseDerivativeLeft E (B x).inverse (fderiv ℝ B x)) (B x).inverse := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact actualInverseField_fderiv hB hx u v

end Yau.Blueprint.C02Proof
