import Yau.Proofs.F04PositiveSmoothing
import Yau.Proofs.F04DirichletPosPart

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The completed differential of the supported positive part is the genuine
strict-active-set multiplier.  This is proved by smooth graph limits. -/
theorem dirichletPosPart_D (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O) :
    dirichletD g μ hμ O (dirichletPosPart g μ hμ O hO u) =
      positiveFormMultiplier g (μ.restrict O) (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u) := by
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hl : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hJ : Tendsto (fun j => dirichletL2 g μ hμ O (dirichletPositiveSmoothing g μ hμ O (δ j) u))
      atTop (𝓝 (Lp.posPart (dirichletL2 g μ hμ O u))) := by
    simpa only [dirichletPositiveSmoothing_L2] using
      smoothPositiveL2_tendsto (μ.restrict O) (dirichletL2 g μ hμ O u) δ hδ hl
  have hD := dirichletPositiveSmoothing_D_tendsto g μ hμ O u δ hδ hl
  have hm := (dirichletGraphMap_isClosed_range g μ hμ O).mem_of_tendsto
    (hJ.prodMk_nhds hD) (Eventually.of_forall fun j =>
      show (dirichletL2 g μ hμ O (dirichletPositiveSmoothing g μ hμ O (δ j) u),
        dirichletD g μ hμ O (dirichletPositiveSmoothing g μ hμ O (δ j) u)) ∈
        range (dirichletGraphMap g μ hμ O) from ⟨dirichletPositiveSmoothing g μ hμ O (δ j) u, rfl⟩)
  obtain ⟨v, hv⟩ := hm
  have hPv : dirichletPosPart g μ hμ O hO u = v :=
    dirichletPosPart_unique g hK μ hμ O hO u v (congrArg Prod.fst hv)
  rw [hPv]
  exact congrArg Prod.snd hv

/-- The exact differential formula holds for every actual L2 section
representing Du; membership of the active section is an output. -/
theorem dirichlet_posPart_differential (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O)
    (A : RealForm M 1) (hA : L2RealForm g.form (μ.restrict O) A)
    (hDu : dirichletD g μ hμ O u =
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection A hA)) :
    ∃ hAp : L2RealForm g.form (μ.restrict O)
      (fun x => if 0 < dirichletL2 g μ hμ O u x then A x else 0),
      dirichletD g μ hμ O (dirichletPosPart g μ hμ O hO u) =
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection
          (fun x => if 0 < dirichletL2 g μ hμ O u x then A x else 0) hAp) := by
  refine ⟨positive_active_form_l2 g (μ.restrict O) (dirichletL2 g μ hμ O u) A hA, ?_⟩
  rw [dirichletPosPart_D g hK μ hμ O hO u, hDu, positiveFormMultiplier_realize]

/-- Smooth one-sided approximations converge in the original energy norm,
including their actual exterior derivatives. -/
theorem dirichletPositiveSmoothing_tendsto (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) (u : DirichletEnergy g μ hμ O)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => dirichletPositiveSmoothing g μ hμ O (δ j) u)
      atTop (𝓝 (dirichletPosPart g μ hμ O hO u)) := by
  apply dirichlet_tendsto_of_graph_tendsto g μ hμ O
  · rw [(dirichletPosPart_spec g μ hμ O hO u).1]
    simpa only [dirichletPositiveSmoothing_L2] using
      smoothPositiveL2_tendsto (μ.restrict O) (dirichletL2 g μ hμ O u) δ hδ hlim
  · rw [dirichletPosPart_D g hK μ hμ O hO u]
    exact dirichletPositiveSmoothing_D_tendsto g μ hμ O u δ hδ hlim

end Yau.F04Proof
