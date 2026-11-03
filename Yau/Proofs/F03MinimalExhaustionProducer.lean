import Yau.Proofs.F03MinimalKernelEquation
import Yau.Proofs.F03MinimalKernelSmoothLimit
import Yau.Proofs.F03MinimalKernelInitial
import Yau.Proofs.F03MinimalKernelSemigroup

/-! The original minimal-exhaustion producer on every supplied smooth exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalKernelCandidate_scalarHeatKernel
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    ScalarHeatKernel g.form μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  refine ⟨?_,?_,?_⟩
  · intro y
    refine ⟨kernelSmooth_univ_smoothSpaceTime _
      (dirichletMinimalKernelCandidate_joint_smooth g hK μ hμ O hO) y,?_⟩
    intro x t ht
    exact ⟨dirichletMinimalKernelCandidate_strict_pos g hK μ hμ O hO ht x y,
      (dirichletMinimalKernelCandidate_hasDerivAt g hK μ hμ O hO ht x y).deriv⟩
  · intro t ht x y
    exact dirichletMinimalKernelCandidate_symm g hK μ hμ O hO ht x y
  · intro f hf hcf y
    exact dirichletMinimalKernelCandidate_compact_initial g hK μ hμ O hO f hf hcf y

theorem dirichletMinimalKernelCandidate_positiveTimeOutput
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    MinimalKernelPositiveTimeOutput g.form μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  refine ⟨dirichletMinimalKernelCandidate_scalarHeatKernel g hK μ hμ O hO,?_,?_,?_⟩
  · intro x y
    simpa [KernelSmoothOn] using
      (dirichletMinimalKernelCandidate_joint_smooth g hK μ hμ O hO x y)
  · intro t ht x
    exact dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x
  · intro b c hb hc x y
    exact dirichletMinimalKernelCandidate_semigroup g hK μ hμ O hO hb hc x y

theorem dirichletMinimalKernelCandidate_correct
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    MinimalExhaustionOutput g.form μ O (dirichletExhaustionKernels g hK μ hμ O hO)
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  refine ⟨hO,dirichletExhaustionKernels_correct g hK μ hμ O hO,?_,
    dirichletMinimalKernelCandidate_localSmoothLimit g hK μ hμ O hO,
    dirichletMinimalKernelCandidate_positiveTimeOutput g hK μ hμ O hO⟩
  intro t ht x y
  exact ⟨dirichletExhaustionKernels_monotone g hK μ hμ O hO ht x y,
    dirichletExhaustionKernels_tendsto g hK μ hμ O hO ht x y⟩

theorem MinimalExhaustionTarget_native (X : KahlerManifold n) : MinimalExhaustionTarget X := by
  intro μ hμ O hO
  exact ⟨dirichletExhaustionKernels X.metric X.kahler_metric μ hμ O hO,
    dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO,
    dirichletMinimalKernelCandidate_correct X.metric X.kahler_metric μ hμ O hO⟩

end Yau.Proofs.F03Aux
