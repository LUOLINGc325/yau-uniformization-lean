import Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsCalculus
import Yau.LeafProofs.L17BootstrapPatch
import Yau.LeafProofs.L17BootstrapHessianChainInverse

/-! The total actual inverse differential and the true translation Hessian. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

namespace Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux
open L17Aux L17BootstrapPatchAux L17SmallTranslationAux L17BootstrapHessianChainAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)

def inverseDifferential (theta z : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  fderiv ℝ (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound theta) (cutoffTranslation D.bump theta z)

def translationHessian (theta z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta)) z

theorem inverseDifferential_eq_inverseJacobian {theta : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (z : ComplexVector n) :
    inverseDifferential D theta z = inverseJacobian D.bump D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta
      (htheta.trans_le D.smallRadius_le_translation) z :=
  cutoffInverse_fderiv_at_translation D.bump D.bump_smooth D.bound
    (zero_le_one.trans D.bound_ge_one) D.derivative_bound
    (htheta.trans_le D.smallRadius_le_translation) z

theorem inverseDifferential_norm_le {theta : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (z : ComplexVector n) :
    ‖inverseDifferential D theta z‖ ≤ 2 :=
  cutoffInverse_fderiv_norm_le D.bump D.bump_smooth D.bound
    (zero_le_one.trans D.bound_ge_one) D.derivative_bound
    (htheta.trans_le D.smallRadius_le_translation) _

theorem inverseDifferential_contDiffAt {theta : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (z : ComplexVector n) :
    ContDiffAt ℝ ∞ (fun a : ComplexVector n × ComplexVector n => inverseDifferential D a.1 a.2)
      (theta,z) := by
  have hpsi := cutoffInverse_joint_contDiffAt D.bump D.bump_smooth D.bound
    (zero_le_one.trans D.bound_ge_one) D.derivative_bound
    (htheta.trans_le D.smallRadius_le_translation) (cutoffTranslation D.bump theta z)
  have hDpsi := partial_fderiv_contDiffAt hpsi
  exact hDpsi.comp (theta,z)
    (contDiffAt_fst.prodMk (cutoffTranslation_joint_contDiff D.bump_smooth).contDiffAt)

theorem inverseDifferential_contDiffOn :
    ContDiffOn ℝ ∞ (fun a : ComplexVector n × ComplexVector n => inverseDifferential D a.1 a.2)
      (ball (0:ComplexVector n) D.smallRadius ×ˢ (univ : Set (ComplexVector n))) := by
  intro a ha
  exact (inverseDifferential_contDiffAt D
    (by simpa only [mem_ball,dist_zero_right] using ha.1) a.2).contDiffWithinAt

theorem translationHessian_contDiff :
    ContDiff ℝ ∞ (fun a : ComplexVector n × ComplexVector n => translationHessian D a.1 a.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  exact partial_fderiv_contDiffAt (partial_fderiv_contDiffAt
    (cutoffTranslation_joint_contDiff D.bump_smooth).contDiffAt)

theorem inverseDifferential_zero (z : ComplexVector n) :
    inverseDifferential D 0 z = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  have hzero : cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
      D.derivative_bound 0 = id := funext
    (cutoffInverse_zero_parameter D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound)
  simp only [inverseDifferential,hzero,fderiv_id]

theorem translationHessian_zero (z : ComplexVector n) : translationHessian D 0 z = 0 := by
  have hzero : cutoffTranslation D.bump (0:ComplexVector n) = id :=
    funext (cutoffTranslation_zero_parameter D.bump)
  have hid : fderiv ℝ (id : ComplexVector n → ComplexVector n) =
      fun _ => ContinuousLinearMap.id ℝ (ComplexVector n) := funext (fun _ => fderiv_id)
  rw [translationHessian,hzero,hid,fderiv_const_apply]

theorem inverseDifferential_of_not_mem_tsupport {theta z : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (hz : z ∉ tsupport D.bump) :
    inverseDifferential D theta z = ContinuousLinearMap.id ℝ (ComplexVector n) := by
  rw [inverseDifferential_eq_inverseJacobian D htheta z]
  have hJ : cutoffTranslationJacobian D.bump theta z = ContinuousLinearMap.id ℝ (ComplexVector n) :=
    (cutoffTranslation_fderiv D.bump_smooth theta z).symm.trans
      (D.coordinate_fderiv_eq_id_of_not_mem_support theta hz)
  apply ContinuousLinearMap.ext
  intro a
  have h := inverse_jacobian_apply D.bump D.bound (zero_le_one.trans D.bound_ge_one)
    D.derivative_bound theta (htheta.trans_le D.smallRadius_le_translation) z a
  simpa only [hJ,ContinuousLinearMap.id_apply] using h

theorem translationHessian_of_not_mem_tsupport (theta : ComplexVector n) {z : ComplexVector n}
    (hz : z ∉ tsupport D.bump) : translationHessian D theta z = 0 :=
  D.coordinate_second_fderiv_eq_zero_of_not_mem_support theta hz

theorem inverseComposition_contDiffAt_two {theta : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (z : ComplexVector n)
    (v : ComplexVector n → ℝ) (hv : ContDiffAt ℝ 2 v z) :
    ContDiffAt ℝ 2 (fun y => v (cutoffInverse D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta y))
      (cutoffTranslation D.bump theta z) := by
  have hsmall := htheta.trans_le D.smallRadius_le_translation
  have hpsi : ContDiffAt ℝ 2 (cutoffInverse D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta)
      (cutoffTranslation D.bump theta z) :=
    (cutoffInverse_contDiff D.bump D.bump_smooth D.bound
    (zero_le_one.trans D.bound_ge_one) D.derivative_bound hsmall).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv' : ContDiffAt ℝ 2 v (cutoffInverse D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta
      (cutoffTranslation D.bump theta z)) := by
    simpa only [cutoffInverse_translation D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound hsmall] using hv
  exact hv'.comp _ hpsi

theorem inverseComposition_hessian {theta : ComplexVector n}
    (htheta : ‖theta‖ < D.smallRadius) (z : ComplexVector n)
    (v : ComplexVector n → ℝ) (hv : ContDiffAt ℝ 2 v z) :
    fderiv ℝ (fderiv ℝ (fun y => v (cutoffInverse D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta y)))
        (cutoffTranslation D.bump theta z) =
      hessianPrecompositionCLM (inverseDifferential D theta z) (fderiv ℝ (fderiv ℝ v) z) +
      gradientCorrectionCLM (inverseDifferential D theta z) (translationHessian D theta z)
        (fderiv ℝ v z) := by
  ext a b
  simpa only [inverseDifferential_eq_inverseJacobian D htheta z,translationHessian,
    add_apply,hessianPrecompositionCLM_apply,gradientCorrectionCLM_apply,sub_eq_add_neg] using
    second_derivative_comp_cutoffInverse_at_translation D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound
      (htheta.trans_le D.smallRadius_le_translation) z v hv a b

end Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux
