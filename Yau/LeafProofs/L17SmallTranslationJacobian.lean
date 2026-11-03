import Yau.LeafProofs.L17SmallTranslationSupport
import Yau.LeafProofs.L17Neumann
import Mathlib.Analysis.Calculus.FDeriv.Mul

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux
open L17NeumannAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cutoffTranslationJacobian (χ : E → ℝ) (θ z : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E+(fderiv ℝ χ z).smulRight θ

theorem cutoffTranslation_hasFDerivAt {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ z : E) :
    HasFDerivAt (cutoffTranslation χ θ) (cutoffTranslationJacobian χ θ z) z :=
  (hasFDerivAt_id z).add (((hχ.differentiable (by simp)) z).hasFDerivAt.smul_const θ)

theorem cutoffTranslation_fderiv {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ z : E) :
    fderiv ℝ (cutoffTranslation χ θ) z=cutoffTranslationJacobian χ θ z :=
  (cutoffTranslation_hasFDerivAt hχ θ z).fderiv

theorem cutoffTranslation_error_norm_lt {χ : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    ‖(fderiv ℝ χ z).smulRight θ‖ < 1/4 := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_mul_of_nonneg_right (hDf z) (norm_nonneg θ)).trans_lt
    (smallTranslation_parameter_bound hL hθ)

variable [CompleteSpace E]

def cutoffJacobianEquiv (χ : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) (θ : E) (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) : E ≃L[ℝ] E :=
  neumannEquiv ((fderiv ℝ χ z).smulRight θ)
    ((cutoffTranslation_error_norm_lt hL hDf hθ z).trans (by norm_num))

@[simp] theorem cutoffJacobianEquiv_toCLM (χ : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) (θ : E) (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    (cutoffJacobianEquiv χ L hL hDf θ hθ z).toContinuousLinearMap=cutoffTranslationJacobian χ θ z := rfl

theorem cutoffJacobianEquiv_symm_norm_le (χ : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) (θ : E) (hθ : ‖θ‖ < smallTranslationRadius L) (z : E) :
    ‖(cutoffJacobianEquiv χ L hL hDf θ hθ z).symm.toContinuousLinearMap‖ ≤ 2 := by
  change ‖neumannSeries ((fderiv ℝ χ z).smulRight θ)‖ ≤ 2
  exact (neumann_norm_le_four_thirds (cutoffTranslation_error_norm_lt hL hDf hθ z).le).trans (by norm_num)

theorem cutoffTranslation_second_derivative {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (θ z a b : E) :
    fderiv ℝ (fderiv ℝ (cutoffTranslation χ θ)) z a b=
      (fderiv ℝ (fderiv ℝ χ) z a b) • θ := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) := (ContinuousLinearMap.smulRightL ℝ E E).flip θ
  have hχD : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hd := ((hχD.differentiable (by simp)) z).hasFDerivAt
  have hR := R.hasFDerivAt.comp z hd
  have hsum := (hasFDerivAt_const (ContinuousLinearMap.id ℝ E) z).add hR
  have hsum' : HasFDerivAt (fun w => ContinuousLinearMap.id ℝ E+R (fderiv ℝ χ w))
      (R.comp (fderiv ℝ (fderiv ℝ χ) z)) z := by
    convert hsum using 1
    · funext w
      rfl
    · simp
  have hFun : fderiv ℝ (cutoffTranslation χ θ)=
      (fun w => ContinuousLinearMap.id ℝ E+R (fderiv ℝ χ w)) := by
    funext w
    rw [cutoffTranslation_fderiv hχ θ w]
    rfl
  rw [hFun,hsum'.fderiv]
  rfl

end Yau.LeafProofs.L17SmallTranslationAux
