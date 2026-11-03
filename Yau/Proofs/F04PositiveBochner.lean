import Yau.Proofs.F04PositiveContinuity
import Yau.Proofs.F04BochnerComposition
import Yau.Proofs.F04BochnerL2

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The supported positive part preserves actual strong L2 convergence on
the finite physical time measure, in the genuine energy norm. -/
theorem dirichlet_posPart_strongL2 (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    {Z : Type*} [MeasurableSpace Z] (τ : Measure Z) [IsFiniteMeasure τ]
    (U : ℕ → Z → DirichletEnergy g μ hμ O) (u : Z → DirichletEnergy g μ hμ O)
    (hU : ∀ j, MemLp (U j) 2 τ) (hu : MemLp u 2 τ)
    (hlim : Tendsto (fun j => ∫ t, ‖U j t - u t‖ ^ 2 ∂τ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ t,
      ‖dirichletPosPart g μ hμ O hO (U j t) - dirichletPosPart g μ hμ O hO (u t)‖ ^ 2 ∂τ)
      atTop (𝓝 0) := by
  have he := bochner_eLpNorm_tendsto_of_integral U u hU hu hlim
  have ht := continuous_normContractive_comp_L2 τ (dirichletPosPart g μ hμ O hO)
    (continuous_dirichletPosPart g hK μ hμ O hO) (dirichletPosPart_norm_le g μ hμ O hO)
    U u hU hu he
  exact bochner_integral_tendsto_of_eLpNorm
    (fun j t => dirichletPosPart g μ hμ O hO (U j t))
    (fun t => dirichletPosPart g μ hμ O hO (u t))
    (fun j => dirichletPosPart_memLp g hK μ hμ O hO τ (U j) (hU j))
    (dirichletPosPart_memLp g hK μ hμ O hO τ u hu) ht

end Yau.F04Proof
