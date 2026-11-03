import Yau.LeafProofs.L17BootstrapTransportRawHolder
import Yau.LeafProofs.L17BootstrapTransportProfiles

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17LocalHolderAlgebraAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
theorem rawLocal_add_value {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u v : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    localFun F (u+v) q=localFun F u q+localFun F v q := rfl

theorem rawLocal_sub_value {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u v : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    localFun F (u-v) q=localFun F u q-localFun F v q := rfl

variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
variable (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)

theorem correctionValue_eq_scaled_raw (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    correctionValue D theta u (z,t)=P.radius^2*
      localFun ℝ (rawCorrectionValue D htheta hgamma0 hgamma1 u) ⟨D.center,(z,t)⟩ := by
  change P.radius^2*holderFun u.val.1.1 (P.charts.chart D.center (cutoffTranslation D.bump theta z),t)-
    P.radius^2*holderFun u.val.1.1 (P.charts.chart D.center z,t)=P.radius^2*
      (holderFun u.val.1.1 (P.charts.chart D.center (cutoffTranslation D.bump theta z),t)-
        holderFun u.val.1.1 (P.charts.chart D.center z,t))
  ring

theorem correctionTime_eq_raw (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    correctionTime D theta u (z,t)=
      localFun ℝ (rawCorrectionTime D htheta hgamma0 hgamma1 u) ⟨D.center,(z,t)⟩ := rfl

theorem correctionGradient_eq_scaled_raw (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    correctionGradient D theta u (z,t)=P.radius •
      localFun (D1 n) (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u) ⟨D.center,(z,t)⟩ := by
  have hz := D.coordinate_mapsTo_ball htheta z.property
  rw [correctionGradient,chartGradient,chartGradient,dite_eq_left hz,dite_eq_left z.property]
  ext a
  rw [show localFun (D1 n) (rawCorrectionGradient D htheta hgamma0 hgamma1 hTime hr u)
      ⟨D.center,(z,t)⟩=
      (localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)).comp
        (fderiv ℝ (cutoffTranslation D.bump theta) z)-localFun (D1 n) u.val.1.2 ⟨D.center,(z,t)⟩ by
    simp only [rawCorrectionGradient,rawLocal_sub_value,localBilinearElement_value,coordinateJacobianHolder_value,
      localPullbackCLM_value]
    rfl]
  rw [cutoffTranslation_fderiv D.bump_smooth theta z]
  change P.radius*localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
      (cutoffTranslationJacobian D.bump theta z a)-P.radius*localFun (D1 n) u.val.1.2 ⟨D.center,(z,t)⟩ a=
    P.radius*(localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
      (cutoffTranslationJacobian D.bump theta z a)-localFun (D1 n) u.val.1.2 ⟨D.center,(z,t)⟩ a)
  ring

theorem correctionHessian_eq_raw (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    correctionHessian D theta u (z,t)=
      localFun (D2 n) (rawCorrectionHessian D htheta hgamma0 hgamma1 hTime hr u) ⟨D.center,(z,t)⟩ := by
  have hz := D.coordinate_mapsTo_ball htheta z.property
  rw [correctionHessian,chartGradient,chartHessian,chartHessian,dite_eq_left hz,
    dite_eq_left hz,dite_eq_left z.property]
  ext a b
  simp only [rawCorrectionHessian,rawLocal_sub_value,rawLocal_add_value,localBilinearElement_value,coordinateJacobianHolder_value,
    localPullbackCLM_value,_root_.sub_apply,_root_.add_apply,forwardHessian_apply]
  rw [cutoffTranslation_fderiv D.bump_smooth theta z]
  change localFun (D2 n) u.val.2.1 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
      (cutoffTranslationJacobian D.bump theta z a) (cutoffTranslationJacobian D.bump theta z b)+
      P.radius*localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
        (fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta)) z a b)-
      localFun (D2 n) u.val.2.1 ⟨D.center,(z,t)⟩ a b=
    localFun (D2 n) u.val.2.1 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
      (cutoffTranslationJacobian D.bump theta z a) (cutoffTranslationJacobian D.bump theta z b)+
      localFun (D1 n) u.val.1.2 (translatedLocalPoint D htheta ⟨D.center,(z,t)⟩)
        (P.radius • fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta)) z a b)-
      localFun (D2 n) u.val.2.1 ⟨D.center,(z,t)⟩ a b
  rw [map_smul,smul_eq_mul]

end Yau.LeafProofs.L17BootstrapTransportAux
