import Yau.LeafProofs.L17BootstrapTransportRawValues
import Yau.LeafProofs.L17BootstrapTransportPointwiseAlgebra
import Yau.LeafProofs.L17BootstrapTransportPullbackSup

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17LocalHolderAlgebraAux
attribute [local instance] transportRawD1NormedAddCommGroup transportRawD1NormedSpace
  transportRawD2NormedAddCommGroup transportRawD2NormedSpace
  transportRawEndNormedAddCommGroup transportRawEndNormedSpace
  transportRawKNormedAddCommGroup transportRawKNormedSpace
  transportRawEndD1NormedAddCommGroup transportRawEndD1NormedSpace
  transportRawEndD2NormedAddCommGroup transportRawEndD2NormedSpace
  transportRawKD2NormedAddCommGroup transportRawKD2NormedSpace
  transportRawD2D2NormedAddCommGroup transportRawD2D2NormedSpace
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
variable (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)

theorem rawCorrectionGradient_value (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    localFun (D1 n) (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u) q=
      (localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta q)).comp
        (fderiv ℝ (cutoffTranslation D.bump theta) q.2.1)-localFun (D1 n) u.val.1.2 q := by
  simp only [rawCorrectionGradient,rawLocal_sub_value,localBilinearElement_value,
    localPullbackCLM_value,coordinateJacobianHolder_value]
  rfl

theorem rawCorrectionHessian_value (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    localFun (D2 n) (rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u) q=
      precomposeHessian (fderiv ℝ (cutoffTranslation D.bump theta) q.2.1)
        (fderiv ℝ (cutoffTranslation D.bump theta) q.2.1)
        (localFun (D2 n) u.val.2.1 (translatedLocalPoint D htheta q))+
      gradientHessianComposition (localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta q))
        (scaledCoordinateHessian D theta q.2.1)-localFun (D2 n) u.val.2.1 q := by
  simp only [rawCorrectionHessian,rawLocal_sub_value,rawLocal_add_value,localBilinearElement_value,
    localPullbackCLM_value,coordinateJacobianHolder_value]
  rfl

theorem gradientHessianComposition_norm_le (p : D1 n)
    (K : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) :
    ‖gradientHessianComposition p K‖ ≤ ‖p‖*‖K‖ := by
  have hPost : ‖(ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ) p‖ ≤ ‖p‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg p)
    intro J
    exact p.opNorm_comp_le J
  exact (((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ) p).opNorm_comp_le K).trans
    (mul_le_mul_of_nonneg_right hPost (norm_nonneg K))

theorem rawCorrectionValue_sup_le (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    ‖localFun ℝ (rawCorrectionValue D htheta hgamma0 hgamma1 u) q‖ ≤
      ‖u‖*(‖theta‖/P.radius)^gamma := by
  exact (localPullback_difference_value_bound D htheta hgamma0 (rawFunctionLocal u) q).trans
    (mul_le_mul_of_nonneg_right (rawFunctionLocal_norm_le u)
      (Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) _))

theorem rawCorrectionTime_sup_le (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    ‖localFun ℝ (rawCorrectionTime D htheta hgamma0 hgamma1 u) q‖ ≤
      ‖u‖*(‖theta‖/P.radius)^gamma := by
  exact (localPullback_difference_value_bound D htheta hgamma0 (rawTimeLocal u) q).trans
    (mul_le_mul_of_nonneg_right (rawTimeLocal_norm_le u)
      (Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) _))

theorem rawCorrectionGradient_sup_le (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    ‖localFun (D1 n) (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u) q‖ ≤
      (2+D.bound*P.radius)*‖u‖*(‖theta‖/P.radius)^gamma := by
  have hB := zero_le_one.trans D.bound_ge_one
  have heps := Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) gamma
  have hdiff := (localPullback_difference_value_bound D htheta hgamma0 u.val.1.2 q).trans
    (mul_le_mul_of_nonneg_right (rawGradient_norm_le u) heps)
  have hp := (localValue_norm_le (D1 n) u.val.1.2 q).trans (rawGradient_norm_le u)
  have hJ := D.coordinate_fderiv_norm_le htheta (q.2.1 : ComplexVector n)
  have hErr := D.coordinate_fderiv_error_norm_le theta (q.2.1 : ComplexVector n)
  have ht := theta_norm_le_radius_rpow D htheta hgamma1
  rw [rawCorrectionGradient_value]
  apply (gradient_precompose_sub_norm_le _ _ _).trans
  calc
    _ ≤ (‖u‖*(‖theta‖/P.radius)^gamma)*2+‖u‖*(D.bound*‖theta‖) := by gcongr
    _ ≤ (‖u‖*(‖theta‖/P.radius)^gamma)*2+‖u‖*(D.bound*(P.radius*(‖theta‖/P.radius)^gamma)) := by gcongr
    _ = _ := by ring

theorem rawCorrectionHessian_sup_le (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    ‖localFun (D2 n) (rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u) q‖ ≤
      strongTransportBudget D*‖u‖*(‖theta‖/P.radius)^gamma := by
  have hB := zero_le_one.trans D.bound_ge_one
  have hrho := P.radius_pos.le
  have heps := Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) gamma
  let J := fderiv ℝ (cutoffTranslation D.bump theta) (q.2.1 : ComplexVector n)
  let K := scaledCoordinateHessian D theta (q.2.1 : ComplexVector n)
  let Q := localFun (D2 n) u.val.2.1 q
  let R := localFun (D2 n) u.val.2.1 (translatedLocalPoint D htheta q)
  let p := localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta q)
  have hdiff : ‖R-Q‖ ≤ ‖u‖*(‖theta‖/P.radius)^gamma :=
    (localPullback_difference_value_bound D htheta hgamma0 u.val.2.1 q).trans
      (mul_le_mul_of_nonneg_right (rawHessian_norm_le u) heps)
  have hQ : ‖Q‖ ≤ ‖u‖ := (localValue_norm_le (D2 n) u.val.2.1 q).trans (rawHessian_norm_le u)
  have hp : ‖p‖ ≤ ‖u‖ := (localValue_norm_le (D1 n) u.val.1.2 _).trans (rawGradient_norm_le u)
  have hJ : ‖J‖ ≤ 2 := D.coordinate_fderiv_norm_le htheta _
  have hJ2 : ‖J‖^2 ≤ 4 := by nlinarith [norm_nonneg J]
  have hJ1 : ‖J‖+1 ≤ 3 := by linarith
  have hErr : ‖J-ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ D.bound*‖theta‖ :=
    D.coordinate_fderiv_error_norm_le theta _
  have hK : ‖K‖ ≤ P.radius*D.bound*‖theta‖ := scaledCoordinateHessian_norm_le D theta _
  have ht := theta_norm_le_radius_rpow D htheta hgamma1
  rw [rawCorrectionHessian_value]
  change ‖precomposeHessian J J R+gradientHessianComposition p K-Q‖ ≤ _
  rw [show precomposeHessian J J R+gradientHessianComposition p K-Q=
    (precomposeHessian J J R-Q)+gradientHessianComposition p K by abel]
  apply (norm_add_le _ _).trans
  apply (add_le_add (precomposeHessian_sub_norm_le J Q R) (gradientHessianComposition_norm_le p K)).trans
  calc
    _ ≤ ((‖u‖*(‖theta‖/P.radius)^gamma)*4+‖u‖*(D.bound*‖theta‖)*3)+
        ‖u‖*(P.radius*D.bound*‖theta‖) := by gcongr
    _ ≤ ((‖u‖*(‖theta‖/P.radius)^gamma)*4+‖u‖*(D.bound*(P.radius*(‖theta‖/P.radius)^gamma))*3)+
        ‖u‖*(P.radius*D.bound*(P.radius*(‖theta‖/P.radius)^gamma)) := by gcongr
    _ = _ := by dsimp only [strongTransportBudget]; ring

end Yau.LeafProofs.L17BootstrapTransportAux
