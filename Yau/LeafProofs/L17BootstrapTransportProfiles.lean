import Yau.LeafProofs.L17BootstrapPatchBounds
import Yau.LeafProofs.L17SchauderSpaceNorm

open Set Metric Filter
open scoped ContDiff Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
variable {T γ : ℝ} {hT : 0 < T}

/-- The true finite second chain rule, packaged in the native iterated-CLM model. -/
def forwardHessian (J : ComplexVector n →L[ℝ] ComplexVector n)
    (K : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (p : D1 n) (Q : D2 n) : D2 n :=
  ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ).flip J).comp (Q.comp J)+
    ((ContinuousLinearMap.compL ℝ (ComplexVector n) (ComplexVector n) ℝ) p).comp K

theorem forwardHessian_apply (J : ComplexVector n →L[ℝ] ComplexVector n)
    (K : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (p : D1 n) (Q : D2 n) (a b : ComplexVector n) :
    forwardHessian J K p Q a b=Q (J a) (J b)+p (K a b) := rfl

variable (D : BootstrapPatch P x) (θ : ComplexVector n) (u : SchauderSpace P T γ hT)

def correctionValue (q : ComplexVector n × Time T) : ℝ :=
  chartFunction u D.center q.2 (cutoffTranslation D.bump θ q.1)-chartFunction u D.center q.2 q.1

def correctionGradient (q : ComplexVector n × Time T) : D1 n :=
  (chartGradient u D.center q.2 (cutoffTranslation D.bump θ q.1)).comp
    (cutoffTranslationJacobian D.bump θ q.1)-chartGradient u D.center q.2 q.1

def correctionHessian (q : ComplexVector n × Time T) : D2 n :=
  forwardHessian (cutoffTranslationJacobian D.bump θ q.1)
      (fderiv ℝ (fderiv ℝ (cutoffTranslation D.bump θ)) q.1)
      (chartGradient u D.center q.2 (cutoffTranslation D.bump θ q.1))
      (chartHessian u D.center q.2 (cutoffTranslation D.bump θ q.1))-
    chartHessian u D.center q.2 q.1

def correctionTime (q : ComplexVector n × Time T) : ℝ :=
  timeFun u (P.charts.chart D.center (cutoffTranslation D.bump θ q.1),q.2)-
    timeFun u (P.charts.chart D.center q.1,q.2)

def correctionFamily (q : P.centers) : ComplexVector n × Time T → ℝ :=
  if q=D.center then correctionValue D θ u else 0

def correctionGradientFamily (q : P.centers) : ComplexVector n × Time T → D1 n :=
  if q=D.center then correctionGradient D θ u else 0

def correctionHessianFamily (q : P.centers) : ComplexVector n × Time T → D2 n :=
  if q=D.center then correctionHessian D θ u else 0

def correctionTimeFamily (q : P.centers) : ComplexVector n × Time T → ℝ :=
  if q=D.center then correctionTime D θ u else 0

theorem correctionValue_zero_of_not_mem_support {q : ComplexVector n × Time T}
    (hq : q.1 ∉ tsupport D.bump) : correctionValue D θ u q=0 := by
  have hχ : D.bump q.1=0 := by
    by_contra h
    exact hq (subset_closure h)
  rw [correctionValue,cutoffTranslation_fixed_of_zero D.bump θ hχ,sub_self]

theorem correctionTime_zero_of_not_mem_support {q : ComplexVector n × Time T}
    (hq : q.1 ∉ tsupport D.bump) : correctionTime D θ u q=0 := by
  have hχ : D.bump q.1=0 := by
    by_contra h
    exact hq (subset_closure h)
  rw [correctionTime,cutoffTranslation_fixed_of_zero D.bump θ hχ,sub_self]

theorem correctionGradient_zero_of_not_mem_support {q : ComplexVector n × Time T}
    (hq : q.1 ∉ tsupport D.bump) : correctionGradient D θ u q=0 := by
  have hχ : D.bump q.1=0 := by
    by_contra h
    exact hq (subset_closure h)
  rw [correctionGradient,cutoffTranslation_fixed_of_zero D.bump θ hχ,
    ←cutoffTranslation_fderiv D.bump_smooth θ q.1,
    D.coordinate_fderiv_eq_id_of_not_mem_support θ hq]
  simp only [ContinuousLinearMap.comp_id,sub_self]

theorem correctionHessian_zero_of_not_mem_support {q : ComplexVector n × Time T}
    (hq : q.1 ∉ tsupport D.bump) : correctionHessian D θ u q=0 := by
  have hχ : D.bump q.1=0 := by
    by_contra h
    exact hq (subset_closure h)
  rw [correctionHessian,cutoffTranslation_fixed_of_zero D.bump θ hχ,
    ←cutoffTranslation_fderiv D.bump_smooth θ q.1,
    D.coordinate_fderiv_eq_id_of_not_mem_support θ hq,
    D.coordinate_second_fderiv_eq_zero_of_not_mem_support θ hq]
  apply sub_eq_zero.mpr
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  simp only [forwardHessian_apply,ContinuousLinearMap.id_apply,
    zero_apply,map_zero,add_zero]

theorem correctionValue_hasDerivWithinAt (z : ComplexVector n) (t : Time T) :
    HasDerivWithinAt
      (fun τ => correctionValue D θ u (z,projIcc (0 : ℝ) T hT.le τ))
      (correctionTime D θ u (z,t)) (Icc (0 : ℝ) T) (t : ℝ) := by
  have h1 := schauderFun_hasDerivWithinAt u
    (P.charts.chart D.center (cutoffTranslation D.bump θ z)) t
  have h2 := schauderFun_hasDerivWithinAt u (P.charts.chart D.center z) t
  convert h1.sub h2 using 1 <;> rfl

theorem correctionValue_initial (z : ComplexVector n) :
    correctionValue D θ u (z,⟨0,⟨le_rfl,hT.le⟩⟩)=0 := by
  change schauderFun u (P.charts.chart D.center (cutoffTranslation D.bump θ z),_) -
    schauderFun u (P.charts.chart D.center z,_)=0
  rw [schauderFun_initial,schauderFun_initial,sub_self]

theorem correctionValue_zero_parameter (q : ComplexVector n × Time T) :
    correctionValue D 0 u q=0 := by
  rw [correctionValue,cutoffTranslation_zero_parameter,sub_self]

end Yau.LeafProofs.L17BootstrapTransportAux
