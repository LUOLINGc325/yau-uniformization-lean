import Yau.Proofs.F03MinimalKernelCandidate
import Yau.Proofs.F03MonotoneIntegral

/-! The actual increasing limit retains the original sub-Markov mass bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletMinimalKernelCandidate_mass (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) :
    Integrable (dirichletMinimalKernelCandidate g hK μ hμ O hO t x) μ ∧
      0 ≤ (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y ∂μ) ∧
      (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y ∂μ) ≤ 1 := by
  have h := integrable_monotone_limit_of_integral_le μ
    (fun j => dirichletExhaustionKernels g hK μ hμ O hO j t x)
    (dirichletMinimalKernelCandidate g hK μ hμ O hO t x) 1
    (fun j => (dirichletKernelCandidate_mass g hK μ hμ (O j) (hO.1 j) ht x).1)
    (fun j y => dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 ht x y)
    (fun y => dirichletExhaustionKernels_monotone g hK μ hμ O hO ht x y)
    (fun y => dirichletExhaustionKernels_tendsto g hK μ hμ O hO ht x y)
    (fun j => (dirichletKernelCandidate_mass g hK μ hμ (O j) (hO.1 j) ht x).2)
  exact ⟨h.1,integral_nonneg (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x),h.2⟩

theorem dirichletExhaustionKernels_integral_tendsto (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) :
    Tendsto (fun j => ∫ y, dirichletExhaustionKernels g hK μ hμ O hO j t x y ∂μ) atTop
      (𝓝 (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y ∂μ)) :=
  integral_tendsto_of_tendsto_of_monotone
    (fun j => (dirichletKernelCandidate_mass g hK μ hμ (O j) (hO.1 j) ht x).1)
    (dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x).1
    (ae_of_all μ (dirichletExhaustionKernels_monotone g hK μ hμ O hO ht x))
    (ae_of_all μ (dirichletExhaustionKernels_tendsto g hK μ hμ O hO ht x))

end Yau.Proofs.F03Aux
