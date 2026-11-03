import Yau.LeafProofs.L17BootstrapTransportProfiles

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}

theorem continuousOn_of_local_values {F : Type*} [TopologicalSpace F]
    (f : LocalCylinder P T → F) (hf : Continuous f) (p : P.centers)
    (v : ComplexVector n × Time T → F)
    (hv : ∀ q : ComplexVector n × Time T, ∀ hz : q.1 ∈ ball (0 : ComplexVector n) P.radius,
      v q=f ⟨p,(⟨q.1,hz⟩,q.2)⟩) :
    ContinuousOn v (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
  let S := ball (0 : ComplexVector n) P.radius ×ˢ (univ : Set (Time T))
  have hz : Continuous (fun q : S => (⟨q.val.1,q.property.1⟩ : ↥(ball (0 : ComplexVector n) P.radius))) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have ht : Continuous (fun q : S => q.val.2) := continuous_snd.comp continuous_subtype_val
  have hMap : Continuous (fun q : S => (⟨p,(⟨q.val.1,q.property.1⟩,q.val.2)⟩ : LocalCylinder P T)) :=
    continuous_sigmaMk.comp (hz.prodMk ht)
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hf.comp hMap using 1
  funext q
  exact hv q.val q.property.1

variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)
    (u : SchauderSpace P T gamma hT)

theorem continuous_of_inner_and_zero {F : Type*} [TopologicalSpace F] [Zero F]
    (v : ComplexVector n × Time T → F)
    (hIn : ContinuousOn v (ball (0 : ComplexVector n) P.radius ×ˢ univ))
    (hZero : ∀ q : ComplexVector n × Time T, q.1 ∉ tsupport D.bump → v q=0) : Continuous v := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases hq : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · exact hIn.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)
  · have hK : q.1 ∉ tsupport D.bump := fun h => hq
      ((ball_subset_ball (by linarith [P.radius_pos])) (D.bump_support_ball_quarter h))
    apply (continuousAt_const (y := (0 : F))).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually ((isClosed_tsupport D.bump).isOpen_compl.mem_nhds hK)] with r hr
    exact hZero r hr

theorem chartValue_joint_continuousOn (p : P.centers) :
    ContinuousOn (fun q : ComplexVector n × Time T => chartFunction u p q.2 q.1)
      (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
  apply continuousOn_of_local_values
    (fun q : LocalCylinder P T => schauderFun u (chartPoint P T q.1 q.2))
    (continuous_sigma_iff.mpr (fun p => (schauderFun_continuous u).comp (chartPoint_continuous P T p))) p
  intro q hz
  rfl

theorem chartTime_joint_continuousOn (p : P.centers) :
    ContinuousOn (fun q : ComplexVector n × Time T => timeFun u (P.charts.chart p q.1,q.2))
      (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
  apply continuousOn_of_local_values
    (fun q : LocalCylinder P T => timeFun u (chartPoint P T q.1 q.2))
    (continuous_sigma_iff.mpr (fun p => (timeFun_continuous u).comp (chartPoint_continuous P T p))) p
  intro q hz
  rfl

theorem chartGradient_joint_continuousOn (p : P.centers) :
    ContinuousOn (fun q : ComplexVector n × Time T => chartGradient u p q.2 q.1)
      (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
  apply continuousOn_of_local_values (gradientFun u) (gradientFun_continuous u) p
  intro q hz
  simp only [chartGradient,dite_eq_left hz]

theorem chartHessian_joint_continuousOn (p : P.centers) :
    ContinuousOn (fun q : ComplexVector n × Time T => chartHessian u p q.2 q.1)
      (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
  apply continuousOn_of_local_values (hessianFun u) (hessianFun_continuous u) p
  intro q hz
  simp only [chartHessian,dite_eq_left hz]

def translatedProduct (q : ComplexVector n × Time T) : ComplexVector n × Time T :=
  (cutoffTranslation D.bump theta q.1,q.2)

theorem translatedProduct_continuous : Continuous (translatedProduct D (theta := theta) (T := T)) :=
  ((cutoffTranslation_contDiff D.bump_smooth theta).continuous.comp continuous_fst).prodMk continuous_snd

include htheta in
theorem translatedProduct_mapsTo : MapsTo (translatedProduct D (theta := theta) (T := T))
    (ball (0 : ComplexVector n) P.radius ×ˢ univ) (ball (0 : ComplexVector n) P.radius ×ˢ univ) :=
  fun _q hq => ⟨D.coordinate_mapsTo_ball htheta hq.1,mem_univ _⟩

theorem forwardHessian_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    {J : X → ComplexVector n →L[ℝ] ComplexVector n}
    {K : X → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n}
    {p : X → D1 n} {Q : X → D2 n}
    (hJ : ContinuousOn J S) (hK : ContinuousOn K S)
    (hp : ContinuousOn p S) (hQ : ContinuousOn Q S) :
    ContinuousOn (fun q => forwardHessian (J q) (K q) (p q) (Q q)) S := by
  exact (((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
    (hQ.clm_comp hJ)).add
      (((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).continuous.comp_continuousOn hp).clm_comp hK)

include htheta in
theorem correctionValue_continuous : Continuous (correctionValue D theta u) := by
  apply continuous_of_inner_and_zero D
  · exact ((chartValue_joint_continuousOn u D.center).comp (translatedProduct_continuous D).continuousOn
      (translatedProduct_mapsTo D htheta)).sub (chartValue_joint_continuousOn u D.center)
  · intro q hq
    exact correctionValue_zero_of_not_mem_support D theta u hq

include htheta in
theorem correctionTime_continuous : Continuous (correctionTime D theta u) := by
  apply continuous_of_inner_and_zero D
  · exact ((chartTime_joint_continuousOn u D.center).comp (translatedProduct_continuous D).continuousOn
      (translatedProduct_mapsTo D htheta)).sub (chartTime_joint_continuousOn u D.center)
  · intro q hq
    exact correctionTime_zero_of_not_mem_support D theta u hq

include htheta in
theorem correctionGradient_continuous : Continuous (correctionGradient D theta u) := by
  have hJ : Continuous (fun q : ComplexVector n × Time T => cutoffTranslationJacobian D.bump theta q.1) := by
    have hD : ContDiff ℝ ∞ (fderiv ℝ (cutoffTranslation D.bump theta)) :=
      (cutoffTranslation_contDiff D.bump_smooth theta).fderiv_right (by simp)
    have hEq : cutoffTranslationJacobian D.bump theta=fderiv ℝ (cutoffTranslation D.bump theta) :=
      funext (fun z => (cutoffTranslation_fderiv D.bump_smooth theta z).symm)
    rw [hEq]
    exact hD.continuous.comp continuous_fst
  apply continuous_of_inner_and_zero D
  · exact ((((chartGradient_joint_continuousOn u D.center).comp (translatedProduct_continuous D).continuousOn
      (translatedProduct_mapsTo D htheta)).clm_comp hJ.continuousOn).sub (chartGradient_joint_continuousOn u D.center))
  · intro q hq
    exact correctionGradient_zero_of_not_mem_support D theta u hq

include htheta in
theorem correctionHessian_continuous : Continuous (correctionHessian D theta u) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (cutoffTranslation D.bump theta)) :=
    (cutoffTranslation_contDiff D.bump_smooth theta).fderiv_right (by simp)
  have hDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump theta))) := hD.fderiv_right (by simp)
  have hJ : ContinuousOn (fun q : ComplexVector n × Time T => cutoffTranslationJacobian D.bump theta q.1)
      (ball (0 : ComplexVector n) P.radius ×ˢ univ) := by
    have hEq : cutoffTranslationJacobian D.bump theta=fderiv ℝ (cutoffTranslation D.bump theta) :=
      funext (fun z => (cutoffTranslation_fderiv D.bump_smooth theta z).symm)
    rw [hEq]
    exact (hD.continuous.comp continuous_fst).continuousOn
  apply continuous_of_inner_and_zero D
  · apply (forwardHessian_continuousOn hJ (hDD.continuous.comp continuous_fst).continuousOn
      ((chartGradient_joint_continuousOn u D.center).comp (translatedProduct_continuous D).continuousOn
        (translatedProduct_mapsTo D htheta))
      ((chartHessian_joint_continuousOn u D.center).comp (translatedProduct_continuous D).continuousOn
        (translatedProduct_mapsTo D htheta))).sub (chartHessian_joint_continuousOn u D.center)
  · intro q hq
    exact correctionHessian_zero_of_not_mem_support D theta u hq

end Yau.LeafProofs.L17BootstrapTransportAux
