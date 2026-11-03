import Yau.Proofs.F03MinimalKernelIdentification
import Yau.Proofs.F03CompactHeatPowers

/-! The original minimal-kernel integral is the same actual classical heat for each compact scalar. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalKernelCandidate_compact_evolution
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (k : ScalarEnergyDomain g μ hμ) {t : ℝ} (ht : 0 < t) :
    boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
      (fun y => k y) t=(fun x => wholeCompactHeat g hK μ hμ k x t) := by
  have hf := continuous_compact_scalarL2 g μ hμ univ (continuous_of_smoothFn k.2.1) k.2.2
  funext x
  have hE := dirichletKernelCandidate_evolution_inside g hK μ hμ univ isOpen_univ
    ht x (mem_univ x) k hf
  rw [scalarToLp_eq_restriction_compact g μ hμ univ k hf] at hE
  rw [boundedKernelEvolution,if_neg ht.ne'] at hE ⊢
  exact (integral_congr_ae (ae_of_all μ (fun y =>
    congrArg (fun a : ℝ => a*k y) (dirichletMinimalKernelCandidate_eq_whole g hK μ hμ O hO ht x y)))).trans hE

end Yau.Proofs.F03Aux
