import Yau.Proofs.V03ParameterDerivative
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Joint Bochner integral calculus, also on compact parameter subtypes. -/

open scoped Topology ContDiff
open Filter MeasureTheory Metric

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open V03Proof

theorem continuous_intervalIntegral_of_joint_bounded
    {X F : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : X → ℝ → F} {a b M : ℝ}
    (hf : ContinuousOn (fun p : X × ℝ => f p.1 p.2) (Set.univ ×ˢ Set.uIcc a b))
    (hbound : ∀ x t, t ∈ Set.uIcc a b → ‖f x t‖ ≤ M) :
    Continuous (fun x => ∫ t in a..b, f x t) := by
  have htime : ∀ x, ContinuousOn (f x) (Set.uIcc a b) := by
    intro x
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨Set.mem_univ x, ht⟩)
  have hparam : ∀ t ∈ Set.uIcc a b, Continuous (fun x => f x t) := by
    intro t ht
    apply continuousOn_univ.mp
    exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x _ => ⟨Set.mem_univ x, ht⟩)
  apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => M)
  · intro x
    exact ((htime x).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · intro x
    exact Eventually.of_forall fun t ht => hbound x t (Set.uIoc_subset_uIcc ht)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => hparam t (Set.uIoc_subset_uIcc ht)

theorem differentiableOn_intervalIntegral_of_joint_fderiv
    {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {O : Set P} {f : P → ℝ → F} {a b : ℝ}
    (hO : IsOpen O) (hab : a ≤ b)
    (hf : ContinuousOn (fun p : P × ℝ => f p.1 p.2) (O ×ˢ Set.Icc a b))
    (hd : ∀ t ∈ Set.Icc a b, DifferentiableOn ℂ (fun p => f p t) O)
    (hdc : ContinuousOn (fun p : P × ℝ => fderiv ℂ (fun z => f z p.2) p.1)
      (O ×ˢ Set.Icc a b)) :
    DifferentiableOn ℂ (fun p => ∫ t in a..b, f p t) O := by
  let := FiniteDimensional.proper ℂ P
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO p hp
  have hclosed : closedBall p (r / 2) ⊆ O := by
    intro z hz
    exact hball (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)))
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_intervalIntegral_of_joint_compact
    (f' := fun z t => fderiv ℂ (fun w => f w t) z)
    (isCompact_closedBall p (r / 2)) (closedBall_mem_nhds p (by positivity)) hab
    (hf.mono (Set.prod_mono hclosed Set.Subset.rfl))
    (hdc.mono (Set.prod_mono hclosed Set.Subset.rfl))
  intro z hz t ht
  exact ((hd t ht z (hclosed hz)).differentiableAt (hO.mem_nhds (hclosed hz))).hasFDerivAt

end Yau.Blueprint.V02FlowProof
