import Yau.LeafProofs.L17BootstrapTransportFamilyBounds

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)

include htheta

theorem correctionFamily_localScaledJetBounds (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1) (u : SchauderSpace P T gamma hT) :
    LocalScaledJetBounds P T gamma (2*(transportBudget D*‖u‖)) (correctionFamily D theta u)
      (correctionGradientFamily D theta u) (correctionHessianFamily D theta u)
      (correctionTimeFamily D theta u) := by
  apply correctionFamily_bounds_of_actual_holders D theta u
    (mul_nonneg (transportBudget_pos D).le (norm_nonneg u)) hgamma0 hgamma1
    (rawCorrectionValue D htheta hgamma0 hgamma1 u)
    (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u)
    (rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u)
    (rawCorrectionTime D htheta hgamma0 hgamma1 u)
    (rawCorrection_norms_le D htheta hgamma0 hgamma1 hTime hr u)
  · intro q hq
    simpa only [smul_eq_mul] using correctionValue_eq_scaled_raw D htheta hgamma0 hgamma1 u ⟨q.1,hq⟩ q.2
  · intro q hq
    exact correctionGradient_eq_scaled_raw D htheta hgamma0 hgamma1 hTime hr u ⟨q.1,hq⟩ q.2
  · intro q hq
    exact correctionHessian_eq_raw D htheta hgamma0 hgamma1 hTime hr u ⟨q.1,hq⟩ q.2
  · intro q hq
    exact correctionTime_eq_raw D htheta hgamma0 hgamma1 u ⟨q.1,hq⟩ q.2

theorem correctionFamily_quarterScaledJetBounds (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (u : SchauderSpace P T (1/2) hT) :
    LocalScaledJetBounds P T (1/4) (2*(4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ)))
      (correctionFamily D theta u) (correctionGradientFamily D theta u)
      (correctionHessianFamily D theta u) (correctionTimeFamily D theta u) := by
  have hA : 0 ≤ 4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (mul_nonneg (transportBudget_pos D).le (norm_nonneg u)))
      (Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) _)
  apply correctionFamily_bounds_of_actual_holders D theta u hA
    (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) ≤ 1)
    (quarterCorrectionValue D htheta hTime u)
    (quarterCorrectionGradient D htheta hTime hr u)
    (quarterCorrectionHessian D htheta hTime hr u)
    (quarterCorrectionTime D htheta hTime u)
    (quarterCorrection_norms_le D htheta hTime hr u)
  · intro q hq
    simpa only [quarterCorrectionValue,localWeakenElement_value,smul_eq_mul] using
      correctionValue_eq_scaled_raw D htheta (by norm_num) (by norm_num) u ⟨q.1,hq⟩ q.2
  · intro q hq
    simpa only [quarterCorrectionGradient,localWeakenElement_value] using
      correctionGradient_eq_scaled_raw D htheta (by norm_num) (by norm_num) hTime hr u ⟨q.1,hq⟩ q.2
  · intro q hq
    simpa only [quarterCorrectionHessian,localWeakenElement_value] using
      correctionHessian_eq_raw D htheta (by norm_num) (by norm_num) hTime hr u ⟨q.1,hq⟩ q.2
  · intro q hq
    simpa only [quarterCorrectionTime,localWeakenElement_value] using
      correctionTime_eq_raw D htheta (by norm_num) (by norm_num) u ⟨q.1,hq⟩ q.2

end Yau.LeafProofs.L17BootstrapTransportAux
