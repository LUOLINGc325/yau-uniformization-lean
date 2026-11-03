import Yau.Proofs.F03DirichletKernelLateral
import Yau.Proofs.F03DirichletKernelSmooth
import Yau.Proofs.F03DirichletStrictPositive
import Yau.Proofs.F03DirichletKernelEquation
import Yau.Proofs.F03DirichletKernelMass
import Yau.Proofs.F03DirichletKernelSemigroup
import Yau.Proofs.F03DirichletKernelGenerator
import Yau.Proofs.F03DirichletKernelInitial

/-! The original full Dirichlet kernel producer, from actual constructed native proofs. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletKernelCandidate_correct (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) :
    DirichletScalarKernel g.form μ Ω (dirichletKernelCandidate g hK μ hμ Ω hΩ.1) := by
  refine ⟨dirichletKernelCandidate_smooth g hK μ hμ Ω hΩ.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro b hb x y
    exact ⟨dirichletKernelCandidate_nonneg g hK μ hμ Ω hΩ.1 hb x y,
      fun hx hy => dirichletKernelCandidate_strict_pos g hK μ hμ Ω hΩ.1 hΩ.2.2.1.2 x y hx hy hb,
      dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ.1 hb x y,
      dirichletKernelCandidate_symm g hK μ hμ Ω hΩ.1 hb x y⟩
  · intro b hb x hx y hy
    exact dirichletKernelCandidate_hasDerivAt g hK μ hμ Ω hΩ.1 hb x y hx hy
  · intro b hb y hy p hp
    exact dirichletKernelCandidate_lateral_zero g hK μ hμ Ω hΩ hb y hy p hp
  · intro b hb x
    exact dirichletKernelCandidate_mass g hK μ hμ Ω hΩ hb x
  · intro b c hb hc x y
    exact ⟨dirichletKernelCandidate_convolution_integrable g hK μ hμ Ω hΩ.1 hb hc x y,
      dirichletKernelCandidate_semigroup g hK μ hμ Ω hΩ.1 hb hc x y⟩
  · intro f hf
    exact ⟨fun b hb x hx => dirichletKernelCandidate_source_integrable g hK μ hμ Ω hΩ.1 hb x hx f hf,
      fun b hb => dirichletKernelCandidate_evolution_scalarL2 g hK μ hμ Ω hΩ.1 hb f hf,
      dirichletKernelCandidate_initial_scalarL2DistanceSq g hK μ hμ Ω hΩ.1 f hf⟩
  · intro f w hf hw
    exact dirichletKernelCandidate_generator_iff g hK μ hμ Ω hΩ.1 f w hf hw
  · intro f hf hcf hfΩ y hy
    exact dirichletKernelCandidate_compact_initial g hK μ hμ Ω hΩ.1 f hf hcf hfΩ y hy

theorem DirichletKernelTarget_native (X : KahlerManifold n) : DirichletKernelTarget X := by
  intro μ hμ Ω hΩ
  exact ⟨dirichletKernelCandidate X.metric X.kahler_metric μ hμ Ω hΩ.1,
    dirichletKernelCandidate_correct X.metric X.kahler_metric μ hμ Ω hΩ⟩

end Yau.Proofs.F03Aux
