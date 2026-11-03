import Yau.Proofs.F03MinimalKernelIdentification
import Yau.Proofs.F03DirichletKernelEquation

/-! Both original total-Laplacian equations of the same pointwise increasing kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletMinimalKernelCandidate_hasDerivAt
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    HasDerivAt (fun s => dirichletMinimalKernelCandidate g hK μ hμ O hO s x y)
      (laplacian g.form (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO t z y) x) t := by
  have hd := dirichletKernelCandidate_hasDerivAt g hK μ hμ univ isOpen_univ ht
    x y (mem_univ x) (mem_univ y)
  have hSlice : (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO t z y)=
      (fun z => dirichletKernelCandidate g hK μ hμ univ isOpen_univ t z y) :=
    funext (fun z => dirichletMinimalKernelCandidate_eq_whole g hK μ hμ O hO ht z y)
  rw [hSlice]
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact dirichletMinimalKernelCandidate_eq_whole g hK μ hμ O hO hs x y

theorem dirichletMinimalKernelCandidate_hasDerivAt_right
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    HasDerivAt (fun s => dirichletMinimalKernelCandidate g hK μ hμ O hO s x y)
      (laplacian g.form (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO t x z) y) t := by
  have hd := dirichletMinimalKernelCandidate_hasDerivAt g hK μ hμ O hO ht y x
  have hSlice : (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO t x z)=
      (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO t z x) :=
    funext (fun z => dirichletMinimalKernelCandidate_symm g hK μ hμ O hO ht x z)
  rw [hSlice]
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact dirichletMinimalKernelCandidate_symm g hK μ hμ O hO hs x y

end Yau.Proofs.F03Aux
