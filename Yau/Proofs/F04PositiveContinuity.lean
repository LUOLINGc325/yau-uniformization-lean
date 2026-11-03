import Yau.Proofs.F04ZeroLevel
import Yau.Proofs.F04PositiveIndicatorLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual supported positive part is strongly continuous in the energy
norm.  Zero-level locality supplies the missing indicator limit. -/
theorem continuous_dirichletPosPart (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) :
    Continuous (dirichletPosPart g μ hμ O hO) := by
  apply continuous_iff_seqContinuous.mpr
  intro seq u hseq
  have hJ := ((dirichletL2 g μ hμ O).continuous.tendsto u).comp hseq
  have hD := ((dirichletD g μ hμ O).continuous.tendsto u).comp hseq
  have hJP (v : DirichletEnergy g μ hμ O) := (dirichletPosPart_spec g μ hμ O hO v).1
  apply dirichlet_tendsto_of_graph_tendsto g μ hμ O
  · simpa only [Function.comp_def, hJP] using
      (Lp.continuous_posPart.tendsto (dirichletL2 g μ hμ O u)).comp hJ
  · obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g (μ.restrict O) (dirichletD g μ hμ O u)
    have hz := dirichlet_differential_zero_on_zero_level g hK μ hμ O hO u A hA hrep.symm
    have hi := positiveFormMultiplier_tendsto_on_zero_level g (μ.restrict O)
      (fun j => dirichletL2 g μ hμ O (seq j)) (dirichletL2 g μ hμ O u) hJ A hA hz
      (fun j => dirichletD g μ hμ O (seq j)) (by simpa only [Function.comp_def, hrep] using hD)
    simpa only [Function.comp_def, dirichletPosPart_D g hK μ hμ O hO, hrep] using hi

/-- Supported positive parts of genuine Bochner Lp curves remain in the same
Bochner space, with no assumed spatial differential or measurable lift. -/
theorem dirichletPosPart_memLp (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) {p : ℝ≥0∞}
    (U : Z → DirichletEnergy g μ hμ O) (hU : MemLp U p ν) :
    MemLp (fun t => dirichletPosPart g μ hμ O hO (U t)) p ν := by
  apply hU.of_le ((continuous_dirichletPosPart g hK μ hμ O hO).comp_aestronglyMeasurable
    hU.aestronglyMeasurable)
  exact ae_of_all ν fun t => dirichletPosPart_norm_le g μ hμ O hO (U t)

end Yau.F04Proof
