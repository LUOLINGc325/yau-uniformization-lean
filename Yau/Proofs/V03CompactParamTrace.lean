import Yau.Proofs.V03PartialDerivative
import Yau.Proofs.V03ContinuousMapRegularity

/-! A genuinely jointly regular function yields its actual continuous
trace on a compact parameter piece. Its pointwise parameter derivative is
the native joint within derivative in the open parameter direction. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def compactParamTrace {U : Set P} {J : Set Q} {f : P × Q → F}
    (hf : ContinuousOn f (U ×ˢ J)) (p : P) : C(J, F) := by
  classical
  exact if hp : p ∈ U then
    ⟨fun q => f (p, q), hf.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun q => ⟨hp, q.2⟩)⟩ else 0

theorem compactParamTrace_apply {U : Set P} {J : Set Q} {f : P × Q → F}
    (hf : ContinuousOn f (U ×ˢ J)) {p : P} (hp : p ∈ U) (q : J) :
    compactParamTrace hf p q = f (p, q) := by
  classical
  simp only [compactParamTrace, dif_pos hp, ContinuousMap.coe_mk]

theorem compactParamTrace_continuousOn {U : Set P} {J : Set Q} {f : P × Q → F}
    (hf : ContinuousOn f (U ×ˢ J)) : ContinuousOn (compactParamTrace hf) U := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hh : ContinuousOn (fun p : P × J => f (p.1, p.2)) (U ×ˢ Set.univ) :=
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, p.2.2⟩)
  exact hh.congr (fun p hp => compactParamTrace_apply hf hp.1 p.2)

def spatialParameterDerivative (f : P × Q → F) (U : Set P) (J : Set Q) (p : P × Q) : P →L[ℝ] F :=
  (fderivWithin ℝ f (U ×ˢ J) p).comp ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] Q))

theorem spatialParameterDerivative_contDiffOn {U : Set P} {J : Set Q} {f : P × Q → F}
    (hUJ : UniqueDiffOn ℝ (U ×ˢ J)) (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) :
    ContDiffOn ℝ ∞ (spatialParameterDerivative f U J) (U ×ˢ J) :=
  (hf.fderivWithin hUJ (m := ∞) (by simp)).clm_comp contDiffOn_const

theorem compactParamTrace_pointwise_hasFDerivAt {U : Set P} (hU : IsOpen U)
    {J : Set Q} {f : P × Q → F} (hf : ContDiffOn ℝ ∞ f (U ×ˢ J))
    {p : P} (hp : p ∈ U) (q : J) :
    HasFDerivAt (fun y => compactParamTrace hf.continuousOn y q)
      (spatialParameterDerivative f U J (p, q)) p := by
  have hs := hasFDerivAt_spatial_slice hU hp q.2
    ((hf.differentiableOn (by simp)) (p, q) ⟨hp, q.2⟩)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hp] with y hy
  exact compactParamTrace_apply hf.continuousOn hy q

end Yau.Blueprint.V03Proof
