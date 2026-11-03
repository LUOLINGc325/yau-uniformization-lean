import Yau.Proofs.F04ShiftSmoothingGraph

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

/-- Shifted positive parts belong to the actual supported energy graph,
although the nonnegative smooth shift itself need not have zero trace. -/
theorem dirichlet_shift_posPart_completed_graph
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    ∃ v : DirichletEnergy g μ hμ O,
      dirichletL2 g μ hμ O v = Lp.posPart (dirichletL2 g μ hμ O u - scalarToLp hr2) ∧
      dirichletD g μ hμ O v =
        positiveFormMultiplier g (μ.restrict O) (dirichletL2 g μ hμ O u - scalarToLp hr2)
          (dirichletD g μ hμ O u -
            realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)) := by
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hl : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hv (j : ℕ) := dirichlet_shift_smoothing_graph g μ hμ O hO (δ j) (hδ j) r hr hr0 hr2 hdr2 u
  choose v hJv hDv using hv
  have hJlim : Tendsto (fun j => dirichletL2 g μ hμ O (v j)) atTop
      (𝓝 (Lp.posPart (dirichletL2 g μ hμ O u - scalarToLp hr2))) := by
    simpa only [hJv] using
      smoothPositiveL2_tendsto (μ.restrict O) (dirichletL2 g μ hμ O u - scalarToLp hr2) δ hδ hl
  have hDlim : Tendsto (fun j => dirichletD g μ hμ O (v j)) atTop
      (𝓝 (positiveFormMultiplier g (μ.restrict O) (dirichletL2 g μ hμ O u - scalarToLp hr2)
        (dirichletD g μ hμ O u -
          realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)))) := by
    simpa only [hDv] using positiveSmoothing_multiplier_tendsto g (μ.restrict O)
      (dirichletL2 g μ hμ O u - scalarToLp hr2)
      (dirichletD g μ hμ O u -
        realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)) δ hδ hl
  have hm := (dirichletGraphMap_isClosed_range g μ hμ O).mem_of_tendsto
    (hJlim.prodMk_nhds hDlim) (Eventually.of_forall fun j =>
      show (dirichletL2 g μ hμ O (v j), dirichletD g μ hμ O (v j)) ∈
        range (dirichletGraphMap g μ hμ O) from ⟨v j, rfl⟩)
  obtain ⟨w, hw⟩ := hm
  exact ⟨w, congrArg Prod.fst hw, congrArg Prod.snd hw⟩

/-- The lift is selected from its proved actual graph. Its definition exposes
no choice of gradient, weak derivative or boundary membership to the caller. -/
def dirichletShiftPosPart
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) : DirichletEnergy g μ hμ O :=
  Classical.choose (dirichlet_shift_posPart_completed_graph g μ hμ O hO r hr hr0 hr2 hdr2 u)

theorem dirichletShiftPosPart_spec
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (r : M.Carrier → ℝ) (hr : SmoothFn r) (hr0 : ∀ x ∈ O, 0 ≤ r x)
    (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (u : DirichletEnergy g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u) =
        Lp.posPart (dirichletL2 g μ hμ O u - scalarToLp hr2) ∧
      dirichletD g μ hμ O (dirichletShiftPosPart g μ hμ O hO r hr hr0 hr2 hdr2 u) =
        positiveFormMultiplier g (μ.restrict O) (dirichletL2 g μ hμ O u - scalarToLp hr2)
          (dirichletD g μ hμ O u -
            realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)) :=
  Classical.choose_spec (dirichlet_shift_posPart_completed_graph g μ hμ O hO r hr hr0 hr2 hdr2 u)

end Yau.F04Proof
