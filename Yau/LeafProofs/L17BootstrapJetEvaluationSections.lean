import Yau.LeafProofs.L17BootstrapJetEvaluationFTC
import Yau.LeafProofs.L17SchauderSpaceNorm

open Set Metric MeasureTheory
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapJetEvaluationAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapClosedSlabAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def timeInclusion (T : ℝ) (x : M.Carrier) : C(Time T,Cylinder M T) :=
  ⟨fun t => (x,t),continuous_const.prodMk continuous_id⟩

variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T) (x : M.Carrier)

def valueTimeSectionCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (Time T) ℝ :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ (timeInclusion T x)).comp
    (functionCLM P T gamma hT)

def derivativeTimeSectionCLM : SchauderSpace P T gamma hT →L[ℝ] BoundedContinuousFunction (Time T) ℝ :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ (timeInclusion T x)).comp
    (timeCLM P T gamma hT)

@[simp] theorem valueTimeSectionCLM_apply (u : SchauderSpace P T gamma hT) (t : Time T) :
    valueTimeSectionCLM P T gamma hT x u t=schauderFun u (x,t) := rfl

@[simp] theorem derivativeTimeSectionCLM_apply (u : SchauderSpace P T gamma hT) (t : Time T) :
    derivativeTimeSectionCLM P T gamma hT x u t=timeFun u (x,t) := rfl

theorem valueTimeSectionCLM_norm_le : ‖valueTimeSectionCLM P T gamma hT x‖≤P.radius^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (sq_nonneg _) (norm_nonneg u))).mpr
  intro t
  change ‖schauderFun u (x,t)‖≤P.radius^2*‖u‖
  simpa only [Real.norm_eq_abs] using (function_holder_bounds u).1 (x,t)

theorem derivativeTimeSectionCLM_norm_le : ‖derivativeTimeSectionCLM P T gamma hT x‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg u)).mpr
  intro t
  change ‖timeFun u (x,t)‖≤‖u‖
  simpa only [Real.norm_eq_abs] using (time_holder_bounds u).1 (x,t)

theorem timeSectionFTC (u : SchauderSpace P T gamma hT) (s t : Time T) :
    valueTimeSectionCLM P T gamma hT x u t-valueTimeSectionCLM P T gamma hT x u s=
      ∫ tau in (s:ℝ)..(t:ℝ), derivativeTimeSectionCLM P T gamma hT x u (projIcc 0 T hT.le tau) :=
  timeFTC u x s t

theorem timeSection_hasDerivWithinAt (u : SchauderSpace P T gamma hT) (t : Time T) :
    HasDerivWithinAt (fun tau => valueTimeSectionCLM P T gamma hT x u (projIcc 0 T hT.le tau))
      (derivativeTimeSectionCLM P T gamma hT x u t) (Icc 0 T) (t:ℝ) :=
  schauderFun_hasDerivWithinAt u x t

theorem timeSection_jetFTC {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) (A : Jet E (SchauderSpace P T gamma hT) k) (s t : Time T) :
    jetEvaluate (E := E) (valueTimeSectionCLM P T gamma hT x) k t A-
      jetEvaluate (valueTimeSectionCLM P T gamma hT x) k s A=
      ∫ tau in (s:ℝ)..(t:ℝ),
        jetEvaluate (derivativeTimeSectionCLM P T gamma hT x) k (projIcc 0 T hT.le tau) A :=
  jetEvaluate_timeFTC hT _ _ (timeSectionFTC P T gamma hT x) k A s t

theorem timeSection_jet_hasDerivWithinAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) (A : Jet E (SchauderSpace P T gamma hT) k) (t : Time T) :
    HasDerivWithinAt
      (fun tau => jetEvaluate (E := E) (valueTimeSectionCLM P T gamma hT x) k (projIcc 0 T hT.le tau) A)
      (jetEvaluate (derivativeTimeSectionCLM P T gamma hT x) k t A) (Icc 0 T) (t:ℝ) :=
  jetEvaluate_time_hasDerivWithinAt hT _ _ (timeSectionFTC P T gamma hT x) k A t

end Yau.LeafProofs.L17BootstrapJetEvaluationAux
