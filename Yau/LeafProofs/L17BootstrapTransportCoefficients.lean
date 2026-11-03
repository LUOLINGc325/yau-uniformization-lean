import Yau.LeafProofs.L17BootstrapPatch
import Yau.LeafProofs.L17SpatialCoefficientHolder
import Yau.LeafProofs.L17LocalHolderBanachAlgebraConstants

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17LocalHolderBanachAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
local instance transportCoefficientsEndNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportCoefficientsEndNormedSpace (n : ℕ) :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportCoefficientsHessianNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transportCoefficientsHessianNormedSpace (n : ℕ) :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

variable (D : BootstrapPatch P x) (theta : ComplexVector n)

def coordinateError (z : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n :=
  BootstrapPatch.scalarFormLift theta (fderiv ℝ D.bump z)

theorem coordinateError_eq (z : ComplexVector n) :
    coordinateError D theta z=fderiv ℝ (cutoffTranslation D.bump theta) z-
      ContinuousLinearMap.id ℝ (ComplexVector n) := by
  rw [cutoffTranslation_fderiv D.bump_smooth theta z]
  simp only [cutoffTranslationJacobian,add_sub_cancel_left]
  rfl

theorem coordinateError_continuous : Continuous (coordinateError D theta) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ D.bump) := D.bump_smooth.fderiv_right (by simp)
  exact (BootstrapPatch.scalarFormLift theta).continuous.comp hD.continuous

theorem coordinateError_norm_le (z : ComplexVector n) :
    ‖coordinateError D theta z‖ ≤ D.bound*‖theta‖ := by
  rw [coordinateError_eq]
  exact D.coordinate_fderiv_error_norm_le theta z

theorem coordinateError_sub_norm_le (z w : ComplexVector n) :
    ‖coordinateError D theta z-coordinateError D theta w‖ ≤ D.bound*‖theta‖*‖z-w‖ := by
  change ‖BootstrapPatch.scalarFormLift theta (fderiv ℝ D.bump z)-
    BootstrapPatch.scalarFormLift theta (fderiv ℝ D.bump w)‖ ≤ _
  rw [← map_sub]
  apply ((BootstrapPatch.scalarFormLift theta).le_opNorm _).trans
  exact (mul_le_mul (BootstrapPatch.scalarFormLift_norm_le theta) (D.bump_gradient_sub_norm_le z w)
    (norm_nonneg _) (norm_nonneg theta)).trans_eq (by ring)

def scaledCoordinateHessian (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  P.radius • fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta)) z

theorem scaledCoordinateHessian_continuous : Continuous (scaledCoordinateHessian D theta) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (cutoffTranslation D.bump theta)) :=
    (cutoffTranslation_contDiff D.bump_smooth theta).fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta))) :=
    hD.fderiv_right (by simp)
  exact hDD.continuous.const_smul P.radius

theorem scaledCoordinateHessian_norm_le (z : ComplexVector n) :
    ‖scaledCoordinateHessian D theta z‖ ≤ P.radius*D.bound*‖theta‖ := by
  rw [scaledCoordinateHessian,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
  exact (mul_le_mul_of_nonneg_left (D.coordinate_second_fderiv_norm_le theta z) P.radius_pos.le).trans_eq (by ring)

theorem scaledCoordinateHessian_sub_norm_le (z w : ComplexVector n) :
    ‖scaledCoordinateHessian D theta z-scaledCoordinateHessian D theta w‖ ≤
      (P.radius*D.bound*‖theta‖)*‖z-w‖ := by
  rw [scaledCoordinateHessian,scaledCoordinateHessian,←smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos P.radius_pos]
  exact (mul_le_mul_of_nonneg_left (D.coordinate_second_fderiv_sub_norm_le theta z w) P.radius_pos.le).trans_eq (by ring)

variable {T gamma : ℝ} (hTime : T ≤ P.radius^2) (hgamma1 : gamma ≤ 1) (hr : P.radius ≤ 1)

def coordinateErrorHolder : LocalHolderSpace (ComplexVector n →L[ℝ] ComplexVector n) P T gamma :=
  spatialCoefficientHolder P hTime hgamma1 hr
    (mul_nonneg (zero_le_one.trans D.bound_ge_one) (norm_nonneg theta))
    (fun _ => coordinateError D theta) (fun _ => (coordinateError_continuous D theta).continuousOn)
    (fun _ z _ => coordinateError_norm_le D theta z)
    (fun _ z _ w _ => coordinateError_sub_norm_le D theta z w)

def scaledCoordinateHessianHolder :
    LocalHolderSpace (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) P T gamma :=
  spatialCoefficientHolder P hTime hgamma1 hr
    (mul_nonneg (mul_nonneg P.radius_pos.le (zero_le_one.trans D.bound_ge_one)) (norm_nonneg theta))
    (fun _ => scaledCoordinateHessian D theta)
    (fun _ => (scaledCoordinateHessian_continuous D theta).continuousOn)
    (fun _ z _ => scaledCoordinateHessian_norm_le D theta z)
    (fun _ z _ w _ => scaledCoordinateHessian_sub_norm_le D theta z w)

theorem coefficient_factor_le_four (hgamma0 : 0 ≤ gamma) : 1+(3 : ℝ)^(1-gamma) ≤ 4 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith : 1-gamma ≤ 1)
  rw [Real.rpow_one] at h
  linarith

theorem coordinateErrorHolder_norm_le (hgamma0 : 0 ≤ gamma) :
    ‖coordinateErrorHolder D theta hTime hgamma1 hr‖ ≤ 4*D.bound*‖theta‖ := by
  apply (spatialCoefficientHolder_norm_le P hTime hgamma1 hr _ _ _ _ _).trans
  exact (mul_le_mul_of_nonneg_left (coefficient_factor_le_four hgamma0)
    (mul_nonneg (zero_le_one.trans D.bound_ge_one) (norm_nonneg theta))).trans_eq (by ring)

theorem scaledCoordinateHessianHolder_norm_le (hgamma0 : 0 ≤ gamma) :
    ‖scaledCoordinateHessianHolder D theta hTime hgamma1 hr‖ ≤ 4*P.radius*D.bound*‖theta‖ := by
  apply (spatialCoefficientHolder_norm_le P hTime hgamma1 hr _ _ _ _ _).trans
  exact (mul_le_mul_of_nonneg_left (coefficient_factor_le_four hgamma0)
    (mul_nonneg (mul_nonneg P.radius_pos.le (zero_le_one.trans D.bound_ge_one)) (norm_nonneg theta))).trans_eq (by ring)

def coordinateJacobianHolder : LocalHolderSpace (ComplexVector n →L[ℝ] ComplexVector n) P T gamma :=
  localConst _ P T gamma (ContinuousLinearMap.id ℝ (ComplexVector n))+
    coordinateErrorHolder D theta hTime hgamma1 hr

theorem coordinateJacobianHolder_value (q : LocalCylinder P T) :
    localFun _ (coordinateJacobianHolder D theta hTime hgamma1 hr) q=
      fderiv ℝ (cutoffTranslation D.bump theta) q.2.1 := by
  change ContinuousLinearMap.id ℝ (ComplexVector n)+coordinateError D theta q.2.1=_
  rw [coordinateError_eq]
  abel

theorem coordinateJacobianHolder_norm_le (hgamma0 : 0 ≤ gamma) :
    ‖coordinateJacobianHolder D theta hTime hgamma1 hr‖ ≤ 1+4*D.bound*‖theta‖ := by
  apply (norm_add_le _ _).trans
  exact add_le_add ((localConst_norm_le _ P T gamma _).trans (ContinuousLinearMap.norm_id_le))
    (coordinateErrorHolder_norm_le D theta hTime hgamma1 hr hgamma0)

end Yau.LeafProofs.L17BootstrapTransportAux
