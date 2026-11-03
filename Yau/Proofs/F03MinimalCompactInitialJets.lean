import Yau.Proofs.F03CompactHeatInitialJets
import Yau.Proofs.F03MinimalCompactEvolution

/-! The original minimal-kernel integral has the literal scalar smooth initial face for compact data. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalBoundedHeat_compact_smooth_initial
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (k : ScalarEnergyDomain g μ hμ) :
    ScalarSmoothInitial
      (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => k y))
      (fun y => k y) := by
  refine ⟨?_,?_⟩
  · funext y
    simp [boundedKernelEvolution]
  · intro a K hKc hKt m ε hε
    obtain ⟨δ,hδ,hClose⟩ := wholeCompactHeat_compact_initial_jets g hK μ hμ k a K hKc hKt m ε hε
    refine ⟨δ,hδ,fun t ht htd z hz => ?_⟩
    have hSlice := dirichletMinimalKernelCandidate_compact_evolution g hK μ hμ O hO k ht
    have hFun : (fun w => inChart a
        (boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) (fun y => k y) t) w-
          inChart a (fun y => k y) w)=
        (fun w => wholeCompactHeat g hK μ hμ k (chartInv a w) t-k (chartInv a w)) := by
      funext w
      exact congrArg (fun s : ℝ => s-k (chartInv a w)) (congrFun hSlice (chartInv a w))
    exact (congrArg (fun f => ‖iteratedFDeriv ℝ m f z‖) hFun).trans_lt (hClose t ht htd z hz)

end Yau.Proofs.F03Aux
