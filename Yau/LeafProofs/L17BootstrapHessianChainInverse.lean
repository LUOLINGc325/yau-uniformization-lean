import Yau.LeafProofs.L17BootstrapHessianChain
import Yau.LeafProofs.L17SmallTranslationInverseDerivative

/-! Exact inverse-coordinate Hessians for the actual cutoff translation. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapHessianChainAux
open L17SmallTranslationAux

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- This is the inverse of the existing actual Jacobian equivalence. -/
def inverseJacobian (chi : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ chi z‖ ≤ L)
    (theta : E) (htheta : ‖theta‖ < smallTranslationRadius L) (z : E) : E →L[ℝ] E :=
  (cutoffJacobianEquiv chi L hL hDf theta htheta z).symm.toContinuousLinearMap

theorem jacobian_inverse_apply (chi : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ chi z‖ ≤ L)
    (theta : E) (htheta : ‖theta‖ < smallTranslationRadius L) (z a : E) :
    cutoffTranslationJacobian chi theta z (inverseJacobian chi L hL hDf theta htheta z a) = a := by
  change cutoffJacobianEquiv chi L hL hDf theta htheta z
    ((cutoffJacobianEquiv chi L hL hDf theta htheta z).symm a) = a
  exact (cutoffJacobianEquiv chi L hL hDf theta htheta z).apply_symm_apply a

theorem inverse_jacobian_apply (chi : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ chi z‖ ≤ L)
    (theta : E) (htheta : ‖theta‖ < smallTranslationRadius L) (z a : E) :
    inverseJacobian chi L hL hDf theta htheta z (cutoffTranslationJacobian chi theta z a) = a := by
  change (cutoffJacobianEquiv chi L hL hDf theta htheta z).symm
    (cutoffJacobianEquiv chi L hL hDf theta htheta z a) = a
  exact (cutoffJacobianEquiv chi L hL hDf theta htheta z).symm_apply_apply a

section Translation
variable (chi : E → ℝ) (hchi : ContDiff ℝ ∞ chi) (L : ℝ) (hL : 0 ≤ L)
  (hDf : ∀ z, ‖fderiv ℝ chi z‖ ≤ L)
include hchi

theorem cutoff_pullback_gradient {theta : E} (htheta : ‖theta‖ < smallTranslationRadius L)
    (z : E) (f : E → G) (hf : ContDiffAt ℝ 2 f (cutoffTranslation chi theta z)) (a : E) :
    fderiv ℝ f (cutoffTranslation chi theta z) a =
      fderiv ℝ (fun w => f (cutoffTranslation chi theta w)) z
        (inverseJacobian chi L hL hDf theta htheta z a) := by
  have hTheta : ContDiffAt ℝ 2 (cutoffTranslation chi theta) z :=
    (cutoffTranslation_contDiff hchi theta).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  symm
  rw [fderiv_comp_of_contDiffAt_two hTheta hf, ContinuousLinearMap.comp_apply,
    cutoffTranslation_fderiv hchi theta z, jacobian_inverse_apply chi L hL hDf theta htheta z a]

/-- Solving the true forward second chain rule retains the gradient correction. -/
theorem cutoff_pullback_hessian {theta : E} (htheta : ‖theta‖ < smallTranslationRadius L)
    (z : E) (f : E → G) (hf : ContDiffAt ℝ 2 f (cutoffTranslation chi theta z)) (a b : E) :
    fderiv ℝ (fderiv ℝ f) (cutoffTranslation chi theta z) a b =
      fderiv ℝ (fderiv ℝ (fun w => f (cutoffTranslation chi theta w))) z
        (inverseJacobian chi L hL hDf theta htheta z a)
        (inverseJacobian chi L hL hDf theta htheta z b) -
      fderiv ℝ (fun w => f (cutoffTranslation chi theta w)) z
        (inverseJacobian chi L hL hDf theta htheta z
          (fderiv ℝ (fderiv ℝ (cutoffTranslation chi theta)) z
            (inverseJacobian chi L hL hDf theta htheta z a)
            (inverseJacobian chi L hL hDf theta htheta z b))) := by
  have hTheta : ContDiffAt ℝ 2 (cutoffTranslation chi theta) z :=
    (cutoffTranslation_contDiff hchi theta).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h := second_derivative_comp_of_contDiffAt_two hTheta hf
    (inverseJacobian chi L hL hDf theta htheta z a)
    (inverseJacobian chi L hL hDf theta htheta z b)
  rw [cutoffTranslation_fderiv hchi theta z,
    jacobian_inverse_apply chi L hL hDf theta htheta z a,
    jacobian_inverse_apply chi L hL hDf theta htheta z b] at h
  rw [cutoff_pullback_gradient chi hchi L hL hDf htheta z f hf
    (fderiv ℝ (fderiv ℝ (cutoffTranslation chi theta)) z
      (inverseJacobian chi L hL hDf theta htheta z a)
      (inverseJacobian chi L hL hDf theta htheta z b))] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem cutoff_pullback_hessian_explicit {theta : E}
    (htheta : ‖theta‖ < smallTranslationRadius L)
    (z : E) (f : E → G) (hf : ContDiffAt ℝ 2 f (cutoffTranslation chi theta z)) (a b : E) :
    fderiv ℝ (fderiv ℝ f) (cutoffTranslation chi theta z) a b =
      fderiv ℝ (fderiv ℝ (fun w => f (cutoffTranslation chi theta w))) z
        (inverseJacobian chi L hL hDf theta htheta z a)
        (inverseJacobian chi L hL hDf theta htheta z b) -
      fderiv ℝ (fun w => f (cutoffTranslation chi theta w)) z
        (inverseJacobian chi L hL hDf theta htheta z
          ((fderiv ℝ (fderiv ℝ chi) z
            (inverseJacobian chi L hL hDf theta htheta z a)
            (inverseJacobian chi L hL hDf theta htheta z b)) • theta)) := by
  simpa only [cutoffTranslation_second_derivative hchi] using
    cutoff_pullback_hessian chi hchi L hL hDf htheta z f hf a b

theorem cutoffInverse_fderiv_at_translation {theta : E}
    (htheta : ‖theta‖ < smallTranslationRadius L) (z : E) :
    fderiv ℝ (cutoffInverse chi hchi L hL hDf theta) (cutoffTranslation chi theta z) =
      inverseJacobian chi L hL hDf theta htheta z := by
  rw [cutoffInverse_fderiv chi hchi L hL hDf htheta,
    cutoffInverse_translation chi hchi L hL hDf htheta z]
  rfl

/-- The actual inverse map has the expected native Hessian, including Fin 0. -/
theorem cutoffInverse_second_derivative_at_translation {theta : E}
    (htheta : ‖theta‖ < smallTranslationRadius L) (z a b : E) :
    fderiv ℝ (fderiv ℝ (cutoffInverse chi hchi L hL hDf theta))
        (cutoffTranslation chi theta z) a b =
      -inverseJacobian chi L hL hDf theta htheta z
        (fderiv ℝ (fderiv ℝ (cutoffTranslation chi theta)) z
          (inverseJacobian chi L hL hDf theta htheta z a)
          (inverseJacobian chi L hL hDf theta htheta z b)) := by
  have hpsi : ContDiffAt ℝ 2 (cutoffInverse chi hchi L hL hDf theta)
      (cutoffTranslation chi theta z) :=
    (cutoffInverse_contDiff chi hchi L hL hDf htheta).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h := cutoff_pullback_hessian chi hchi L hL hDf htheta z
    (cutoffInverse chi hchi L hL hDf theta) hpsi a b
  have hId : (fun w => cutoffInverse chi hchi L hL hDf theta (cutoffTranslation chi theta w)) =
      (fun w : E => w) := funext (cutoffInverse_translation chi hchi L hL hDf htheta)
  have hDId : fderiv ℝ (fun w : E => w) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext w
    exact fderiv_fun_id
  rw [hId,hDId] at h
  simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply, ContinuousLinearMap.id_apply, zero_sub] using h

/-- The native inverse-coordinate composition formula used in the coefficient construction. -/
theorem second_derivative_comp_cutoffInverse_at_translation {theta : E}
    (htheta : ‖theta‖ < smallTranslationRadius L) (z : E)
    (v : E → G) (hv : ContDiffAt ℝ 2 v z) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y => v (cutoffInverse chi hchi L hL hDf theta y)))
        (cutoffTranslation chi theta z) a b =
      fderiv ℝ (fderiv ℝ v) z
        (inverseJacobian chi L hL hDf theta htheta z a)
        (inverseJacobian chi L hL hDf theta htheta z b) -
      fderiv ℝ v z
        (inverseJacobian chi L hL hDf theta htheta z
          (fderiv ℝ (fderiv ℝ (cutoffTranslation chi theta)) z
            (inverseJacobian chi L hL hDf theta htheta z a)
            (inverseJacobian chi L hL hDf theta htheta z b))) := by
  have hpsi : ContDiffAt ℝ 2 (cutoffInverse chi hchi L hL hDf theta)
      (cutoffTranslation chi theta z) :=
    (cutoffInverse_contDiff chi hchi L hL hDf htheta).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv' : ContDiffAt ℝ 2 v
      (cutoffInverse chi hchi L hL hDf theta (cutoffTranslation chi theta z)) := by
    simpa only [cutoffInverse_translation chi hchi L hL hDf htheta] using hv
  have h := second_derivative_comp_of_contDiffAt_two hpsi hv' a b
  rw [cutoffInverse_translation chi hchi L hL hDf htheta z,
    cutoffInverse_fderiv_at_translation chi hchi L hL hDf htheta z,
    cutoffInverse_second_derivative_at_translation chi hchi L hL hDf htheta z a b] at h
  simpa only [map_neg, sub_eq_add_neg] using h

end Translation
end Yau.LeafProofs.L17BootstrapHessianChainAux
