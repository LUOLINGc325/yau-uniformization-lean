import Yau.Proofs.F03BoundaryHeatLimit
import Yau.Proofs.F03DirichletRieszKernel

/-! The remaining original lateral-zero clause for the ONE actual kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem dirichletKernelCandidate_lateral_zero (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) {t : ℝ} (ht : 0 < t)
    (y : M.Carrier) (hy : y ∈ Ω) (p : M.Carrier) (hp : p ∈ frontier Ω) :
    Tendsto (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ.1 t z y) (𝓝[Ω] p) (𝓝 0) := by
  let f := dirichletHeatEvaluationVector g hK μ hμ Ω hΩ.1 y hy (t/2) (half_pos ht)
  have hf : ∀ᵐ z ∂μ.restrict Ω, 0 ≤ f z :=
    dirichletHeatEvaluationVector_nonneg g hK μ hμ Ω hΩ.1 y hy (t/2) (half_pos ht)
  have hrow : (fun z => dirichletKernelCandidate g hK μ hμ Ω hΩ.1 t z y)=
      (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f z (t/2)) := by
    funext z
    rw [dirichletKernelCandidate_symm g hK μ hμ Ω hΩ.1 ht z y]
    exact congrFun (dirichletKernelCandidate_row_classical g hK μ hμ Ω hΩ.1 ht y hy) z
  rw [hrow]
  exact dirichletClassicalHeat_boundary_zero g hK μ hμ Ω hΩ f hf (half_pos ht) p hp

end Yau.Proofs.F03Aux
