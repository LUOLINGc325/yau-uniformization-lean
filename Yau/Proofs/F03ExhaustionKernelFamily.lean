import Yau.Proofs.F03KernelDomainOrder
import Yau.Proofs.F03ExhaustionCore

/-! Actual full Dirichlet kernels on the ORIGINAL supplied smooth exhaustion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

def dirichletExhaustionKernels (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    ℕ → ℝ → M.Carrier → M.Carrier → ℝ :=
  fun j => dirichletKernelCandidate g hK μ hμ (O j) (hO.1 j).1

theorem dirichletExhaustionKernels_correct (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (j : ℕ) :
    DirichletScalarKernel g.form μ (O j) (dirichletExhaustionKernels g hK μ hμ O hO j) :=
  dirichletKernelCandidate_correct g hK μ hμ (O j) (hO.1 j)

theorem dirichletExhaustionKernels_monotone (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) : Monotone (fun j => dirichletExhaustionKernels g hK μ hμ O hO j t x y) := by
  intro i j hij
  exact dirichletKernelCandidate_mono_domain g hK μ hμ (O i) (O j) (hO.1 i).1 (hO.1 j).1
    (smoothExhaustion_monotone hO hij) ht x y

theorem dirichletExhaustionKernels_le_univ (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) (j : ℕ) :
    dirichletExhaustionKernels g hK μ hμ O hO j t x y ≤
      dirichletKernelCandidate g hK μ hμ Set.univ isOpen_univ t x y :=
  dirichletKernelCandidate_mono_domain g hK μ hμ (O j) Set.univ (hO.1 j).1 isOpen_univ
    (subset_univ _) ht x y

theorem dirichletExhaustionKernels_bddAbove (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    BddAbove (Set.range (fun j => dirichletExhaustionKernels g hK μ hμ O hO j t x y)) := by
  refine ⟨dirichletKernelCandidate g hK μ hμ Set.univ isOpen_univ t x y,?_⟩
  rintro z ⟨j,rfl⟩
  exact dirichletExhaustionKernels_le_univ g hK μ hμ O hO ht x y j

end Yau.Proofs.F03Aux
