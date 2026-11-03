import Yau.Proofs.F03DirichletCompactInitial
import Yau.Proofs.F03DirichletKernelEvolution

/-! The literal compact-continuous delta clause of the one actual kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletKernelCandidate_compact_initial (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f : M.Carrier → ℝ)
    (hf : Continuous f) (hcf : HasCompactSupport f) (hfo : tsupport f ⊆ O)
    (y : M.Carrier) (hy : y ∈ O) :
    Tendsto (fun b => ∫ x, dirichletKernelCandidate g hK μ hμ O hO b x y*f x ∂μ)
      (𝓝[>] 0) (𝓝 (f y)) := by
  let hfL := continuous_compact_scalarL2 g μ hμ O hf hcf
  have hlim : Tendsto (fun b => dirichletClassicalHeat g hK μ hμ O hO (scalarToLp hfL) y b)
      (𝓝[>] 0) (𝓝 (f y)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hclose⟩ := dirichletClassicalHeat_uniform_compact_initial g hK μ hμ O hO f
      hf hcf hfo hfL ε hε
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with b hb hbδ
    simpa only [Real.dist_eq] using hclose b hb hbδ y hy
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb' : 0 < b := hb
  have heq := dirichletKernelCandidate_evolution_inside g hK μ hμ O hO hb' y hy f hfL
  rw [boundedKernelEvolution,if_neg hb'.ne'] at heq
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [dirichletKernelCandidate_symm g hK μ hμ O hO hb' x y]

end Yau.Proofs.F03Aux
