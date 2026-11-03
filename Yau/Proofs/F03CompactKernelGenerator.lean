import Yau.Proofs.F03MinimalCompactEvolution

/-! The actual same-kernel compact-source generator is an ordinary pointwise derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Interval
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_compact_hasDerivAt
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (k : ScalarEnergyDomain g μ hμ) {b : ℝ} (hb : 0 < b) (x : M.Carrier) :
    HasDerivAt (fun r => ∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO r x y*k y ∂μ)
      (∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO b x y*laplacian g.form k y ∂μ) b := by
  have hD := dirichletClassicalHeat_compact_hasDerivAt g hK μ hμ univ isOpen_univ
    ⟨k,subset_univ _⟩ hb x (mem_univ x)
  change HasDerivAt (wholeCompactHeat g hK μ hμ k x)
    (wholeCompactHeat g hK μ hμ (scalarCompactLaplacian g μ hμ k) x b) b at hD
  have hL := congrFun (dirichletMinimalKernelCandidate_compact_evolution g hK μ hμ O hO
    (scalarCompactLaplacian g μ hμ k) hb) x
  rw [boundedKernelEvolution,if_neg hb.ne'] at hL
  rw [← hL] at hD
  exact hD.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds hb] with r hr
    have hr0 : 0 < r := hr
    have hEq := congrFun (dirichletMinimalKernelCandidate_compact_evolution g hK μ hμ O hO k hr) x
    simpa only [boundedKernelEvolution,if_neg hr0.ne'] using hEq)

end Yau.Proofs.F03Aux
