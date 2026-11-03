import Yau.LeafProofs.L17BootstrapJetEvaluationSections

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapJetEvaluationAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapClosedSlabAux

section Generic
variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {T : ℝ} (hT : 0<T)

def parameterEvaluate (L : X →L[ℝ] BoundedContinuousFunction (Time T) ℝ) (V : E → X)
    (k : ℕ) (q : E × ℝ) : Jet E ℝ k :=
  jetEvaluate (E := E) L k (projIcc 0 T hT.le q.2) (parameterJet V k q.1)

theorem parameterEvaluate_continuousOn [FiniteDimensional ℝ E]
    (L : X →L[ℝ] BoundedContinuousFunction (Time T) ℝ) {O : Set E} (hO : IsOpen O)
    {V : E → X} (hV : ContDiffOn ℝ ∞ V O) (k : ℕ) :
    ContinuousOn (parameterEvaluate hT L V k) (O ×ˢ Icc 0 T) := by
  have ht : Continuous (fun q : E × ℝ => projIcc 0 T hT.le q.2) :=
    (continuous_projIcc : Continuous (projIcc (0:ℝ) T hT.le)).comp continuous_snd
  have hj : ContinuousOn (fun q : E × ℝ => parameterJet V k q.1) (O ×ˢ Icc 0 T) :=
    (parameterJet_contDiffOn hO hV k).continuousOn.comp continuousOn_fst (fun _ h => h.1)
  exact (jetEvaluate_continuous L k).comp_continuousOn (ht.continuousOn.prodMk hj)

theorem parameterEvaluate_hasFDerivAt
    (L : X →L[ℝ] BoundedContinuousFunction (Time T) ℝ) {O : Set E} (hO : IsOpen O)
    {V : E → X} (hV : ContDiffOn ℝ ∞ V O) (k : ℕ) {z : E} (hz : z∈O) (t : ℝ) :
    HasFDerivAt (fun y => parameterEvaluate hT L V k (y,t))
      (parameterEvaluate hT L V (k+1) (z,t)) z :=
  (jetMap (E := E) ((BoundedContinuousFunction.evalCLM ℝ (projIcc 0 T hT.le t)).comp L) k).hasFDerivAt.comp z
    (parameterJet_hasFDerivAt hO hV k hz)
end Generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T) (x : M.Carrier)

def valueParameterJet (V : E → SchauderSpace P T gamma hT) (k : ℕ) (q : E × ℝ) : Jet E ℝ k :=
  parameterEvaluate hT (valueTimeSectionCLM P T gamma hT x) V k q

def derivativeParameterJet (V : E → SchauderSpace P T gamma hT) (k : ℕ) (q : E × ℝ) : Jet E ℝ k :=
  parameterEvaluate hT (derivativeTimeSectionCLM P T gamma hT x) V k q

@[simp] theorem valueParameterJet_zero (V : E → SchauderSpace P T gamma hT) (z : E) (t : ℝ) :
    valueParameterJet P T gamma hT x V 0 (z,t)=schauderFun (V z) (x,projIcc 0 T hT.le t) := rfl

@[simp] theorem derivativeParameterJet_zero (V : E → SchauderSpace P T gamma hT) (z : E) (t : ℝ) :
    derivativeParameterJet P T gamma hT x V 0 (z,t)=timeFun (V z) (x,projIcc 0 T hT.le t) := rfl

theorem actual_parameter_jet_family {O : Set E} (hO : IsOpen O)
    (V : E → SchauderSpace P T gamma hT) (hV : ContDiffOn ℝ ∞ V O) :
    (∀ k, ContinuousOn (valueParameterJet P T gamma hT x V k) (O ×ˢ Icc 0 T)) ∧
    (∀ k, ContinuousOn (derivativeParameterJet P T gamma hT x V k) (O ×ˢ Icc 0 T)) ∧
    (∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasFDerivAt (fun y => valueParameterJet P T gamma hT x V k (y,t))
        (valueParameterJet P T gamma hT x V (k+1) (z,t)) z) ∧
    (∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasFDerivAt (fun y => derivativeParameterJet P T gamma hT x V k (y,t))
        (derivativeParameterJet P T gamma hT x V (k+1) (z,t)) z) ∧
    (∀ k z, z∈O → ∀ t, t∈Icc 0 T →
      HasDerivWithinAt (fun tau => valueParameterJet P T gamma hT x V k (z,tau))
        (derivativeParameterJet P T gamma hT x V k (z,t)) (Icc 0 T) t) ∧
    (∀ z t, valueParameterJet P T gamma hT x V 0 (z,t)=
      schauderFun (V z) (x,projIcc 0 T hT.le t)) ∧
    (∀ z t, derivativeParameterJet P T gamma hT x V 0 (z,t)=
      timeFun (V z) (x,projIcc 0 T hT.le t)) := by
  refine ⟨?_,?_,?_,?_,?_,valueParameterJet_zero P T gamma hT x V,
    derivativeParameterJet_zero P T gamma hT x V⟩
  · intro k
    exact parameterEvaluate_continuousOn hT _ hO hV k
  · intro k
    exact parameterEvaluate_continuousOn hT _ hO hV k
  · intro k z hz t _ht
    exact parameterEvaluate_hasFDerivAt hT _ hO hV k hz t
  · intro k z hz t _ht
    exact parameterEvaluate_hasFDerivAt hT _ hO hV k hz t
  · intro k z _hz t ht
    simpa only [valueParameterJet,derivativeParameterJet,parameterEvaluate,projIcc_of_mem hT.le ht] using
      timeSection_jet_hasDerivWithinAt P T gamma hT x k (parameterJet V k z) ⟨t,ht⟩

end Yau.LeafProofs.L17BootstrapJetEvaluationAux
