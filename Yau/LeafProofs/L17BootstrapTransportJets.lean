import Yau.LeafProofs.L17BootstrapTransportProfiles
import Yau.LeafProofs.L17BootstrapHessianChain
import Yau.LeafProofs.L17ParabolicOperatorRegularity

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17BootstrapHessianChainAux L17ParabolicOperatorAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}

 theorem chartGradient_eq_native (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius) :
    chartGradient u p t z=fderiv ℝ (chartFunction u p t) z := by
  simpa only [chartGradient,dite_eq_left hz] using (chartFunction_hasFDerivAt u p t hz).fderiv.symm

 theorem chartHessian_eq_native (u : SchauderSpace P T gamma hT) (p : P.centers) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball (0 : ComplexVector n) P.radius) :
    chartHessian u p t z=fderiv ℝ (fderiv ℝ (chartFunction u p t)) z := by
  simpa only [chartHessian,dite_eq_left hz] using (chartFunction_hasSecondFDerivAt u p t hz).fderiv.symm

variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (u : SchauderSpace P T gamma hT)
include htheta

theorem correctionValue_hasFDerivAt_inside {z : ComplexVector n}
    (hz : z ∈ ball (0 : ComplexVector n) P.radius) (t : Time T) :
    HasFDerivAt (fun w => correctionValue D theta u (w,t)) (correctionGradient D theta u (z,t)) z := by
  have htz := D.coordinate_mapsTo_ball htheta hz
  have h := ((chartFunction_hasFDerivAt u D.center t htz).comp z
    (cutoffTranslation_hasFDerivAt D.bump_smooth theta z)).sub (chartFunction_hasFDerivAt u D.center t hz)
  convert! h using 1
  simp only [correctionGradient,chartGradient,dite_eq_left htz,dite_eq_left hz]

theorem compositionHessian_eq_forward {z : ComplexVector n}
    (hz : z ∈ ball (0 : ComplexVector n) P.radius) (t : Time T) :
    compositionHessian (chartFunction u D.center t) (cutoffTranslation D.bump theta) z=
      forwardHessian (cutoffTranslationJacobian D.bump theta z)
        (fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta)) z)
        (chartGradient u D.center t (cutoffTranslation D.bump theta z))
        (chartHessian u D.center t (cutoffTranslation D.bump theta z)) := by
  have htz := D.coordinate_mapsTo_ball htheta hz
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [compositionHessian_apply,forwardHessian_apply,cutoffTranslation_fderiv D.bump_smooth theta z,
    ←chartGradient_eq_native u D.center t htz,←chartHessian_eq_native u D.center t htz]

theorem correctionGradient_hasFDerivAt_inside {z : ComplexVector n}
    (hz : z ∈ ball (0 : ComplexVector n) P.radius) (t : Time T) :
    HasFDerivAt (fun w => correctionGradient D theta u (w,t)) (correctionHessian D theta u (z,t)) z := by
  have htz := D.coordinate_mapsTo_ball htheta hz
  have hTheta : ContDiffAt ℝ 2 (cutoffTranslation D.bump theta) z :=
    ((cutoffTranslation_contDiff D.bump_smooth theta).contDiffAt).of_le (by simp)
  have hf : ContDiffAt ℝ 2 (chartFunction u D.center t) (cutoffTranslation D.bump theta z) :=
    (chartFunction_contDiffOn_two u D.center t).contDiffAt (isOpen_ball.mem_nhds htz)
  have hBase : HasFDerivAt (fderiv ℝ (chartFunction u D.center t)) (chartHessian u D.center t z) z := by
    simpa only [chartHessian,dite_eq_left hz] using chartFunction_hasSecondFDerivAt u D.center t hz
  have h := (hasFDerivAt_fderiv_comp_of_contDiffAt_two hTheta hf).sub hBase
  rw [compositionHessian_eq_forward D htheta u hz t] at h
  change HasFDerivAt
    (fun w => fderiv ℝ (fun v => chartFunction u D.center t (cutoffTranslation D.bump theta v)) w-
      fderiv ℝ (chartFunction u D.center t) w) (correctionHessian D theta u (z,t)) z at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  have htw := D.coordinate_mapsTo_ball htheta hw
  have hThetaW : ContDiffAt ℝ 2 (cutoffTranslation D.bump theta) w :=
    ((cutoffTranslation_contDiff D.bump_smooth theta).contDiffAt).of_le (by simp)
  have hfW : ContDiffAt ℝ 2 (chartFunction u D.center t) (cutoffTranslation D.bump theta w) :=
    (chartFunction_contDiffOn_two u D.center t).contDiffAt (isOpen_ball.mem_nhds htw)
  rw [fderiv_comp_of_contDiffAt_two hThetaW hfW,cutoffTranslation_fderiv D.bump_smooth theta w,
    ←chartGradient_eq_native u D.center t htw,←chartGradient_eq_native u D.center t hw]
  rfl

theorem correctionValue_hasFDerivAt (z : ComplexVector n) (t : Time T) :
    HasFDerivAt (fun w => correctionValue D theta u (w,t)) (correctionGradient D theta u (z,t)) z := by
  by_cases hz : z ∈ ball (0 : ComplexVector n) P.radius
  · exact correctionValue_hasFDerivAt_inside D htheta u hz t
  · have hK : z ∉ tsupport D.bump := fun h => hz
      ((ball_subset_ball (by linarith [P.radius_pos])) (D.bump_support_ball_quarter h))
    rw [correctionGradient_zero_of_not_mem_support D theta u hK]
    apply (hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport D.bump).isOpen_compl.mem_nhds hK] with w hw
    exact correctionValue_zero_of_not_mem_support D theta u hw

theorem correctionGradient_hasFDerivAt (z : ComplexVector n) (t : Time T) :
    HasFDerivAt (fun w => correctionGradient D theta u (w,t)) (correctionHessian D theta u (z,t)) z := by
  by_cases hz : z ∈ ball (0 : ComplexVector n) P.radius
  · exact correctionGradient_hasFDerivAt_inside D htheta u hz t
  · have hK : z ∉ tsupport D.bump := fun h => hz
      ((ball_subset_ball (by linarith [P.radius_pos])) (D.bump_support_ball_quarter h))
    rw [correctionHessian_zero_of_not_mem_support D theta u hK]
    apply (hasFDerivAt_const (0 : D1 n) z).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport D.bump).isOpen_compl.mem_nhds hK] with w hw
    exact correctionGradient_zero_of_not_mem_support D theta u hw

end Yau.LeafProofs.L17BootstrapTransportAux
