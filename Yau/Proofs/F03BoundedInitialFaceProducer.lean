import Yau.Proofs.F03BoundedInitialJets
import Yau.Proofs.F03MinimalExhaustionProducer

/-! The original bounded-initial-face producer, for the same actual minimal kernel and every bounded smooth datum. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalBoundedHeat_class
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hBounded : ∃ C : ℝ,∀ y,|f y| ≤ C) :
    IsBoundedScalarHeat g.form f
      (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f) := by
  have hfa : AEStronglyMeasurable f μ := (continuous_of_smoothFn hf).aestronglyMeasurable
  obtain ⟨C0,hC0⟩ := hBounded
  let B := max 1 C0
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBound : ∀ y,|f y| ≤ B := fun y => (hC0 y).trans (le_max_right _ _)
  exact ⟨dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO f hfa B hB hBound,
    dirichletMinimalBoundedHeat_smooth_initial g hK μ hμ O hO f hf ⟨C0,hC0⟩,
    (fun _T _hT => ⟨B,hB,fun x t ht _htT =>
      (dirichletMinimalKernelCandidate_bounded_evolution_le g hK μ hμ O hO f hfa B hB.le hBound ht x).2⟩),
    (fun x t ht => dirichletMinimalBoundedHeat_hasDerivAt g hK μ hμ O hO f hfa B hB hBound x ht)⟩

theorem dirichletMinimalKernelCandidate_boundedInitialFaceOutput
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    BoundedInitialFaceOutput g.form μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  intro f hf hBounded
  have hfa : AEStronglyMeasurable f μ := (continuous_of_smoothFn hf).aestronglyMeasurable
  exact ⟨(fun t ht x => dirichletMinimalKernelCandidate_bounded_source_integrable
      g hK μ hμ O hO f hfa hBounded ht x),
    (fun B hB hBound t ht x => dirichletMinimalKernelCandidate_bounded_evolution_le
      g hK μ hμ O hO f hfa B hB hBound ht x),
    dirichletMinimalBoundedHeat_class g hK μ hμ O hO f hf hBounded⟩

theorem BoundedInitialFaceTarget_native (X : KahlerManifold n) : BoundedInitialFaceTarget X := by
  intro μ hμ O hO
  exact ⟨dirichletExhaustionKernels X.metric X.kahler_metric μ hμ O hO,
    dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO,
    dirichletMinimalKernelCandidate_correct X.metric X.kahler_metric μ hμ O hO,
    dirichletMinimalKernelCandidate_boundedInitialFaceOutput X.metric X.kahler_metric μ hμ O hO⟩

end Yau.Proofs.F03Aux
