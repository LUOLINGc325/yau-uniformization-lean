import Yau.Proofs.D02RieszDensity
import Yau.Proofs.D02RieszContinuity

open MeasureTheory Filter Set
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- The actual smooth Laplacian masses converge on every relatively compact
disc whose boundary sphere has zero limiting mass. -/
theorem smoothRieszOn_tendsto_ball {U : Set ℂ} (hU : IsOpen U)
    {v : ℕ → ℂ → ℝ} {μ : Measure ℂ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂smoothRieszOn U (v j)) atTop (𝓝 (∫ z, f z ∂μ)))
    (z : ℂ) (r : ℝ) (hball : Metric.closedBall z r ⊆ U)
    (hzero : μ (Metric.sphere z r) = 0) :
    Tendsto (fun j ↦ smoothRieszOn U (v j) (Metric.ball z r)) atTop
      (𝓝 (μ (Metric.ball z r))) := by
  apply tendsto_mass_of_null_frontier hU
    (fun j K hK hKU ↦ smoothRieszOn_compact_finite hU (hv j) hK hKU) hμ hvague
    ((isCompact_closedBall z r).of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans hball) measurableSet_ball
  exact measure_mono_null Metric.frontier_ball_subset_sphere hzero

/-- The same convergence expressed with the original L08 smooth Riesz measure,
including its exact whole-disc total-mass convention. -/
theorem L08_smoothRieszMeasure_tendsto_mass {U : Set ℂ} (hU : IsOpen U)
    {v : ℕ → ℂ → ℝ} {μ : Measure ℂ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂smoothRieszOn U (v j)) atTop (𝓝 (∫ z, f z ∂μ)))
    (z : ℂ) (r : ℝ) (hball : Metric.closedBall z r ⊆ U)
    (hzero : μ (Metric.sphere z r) = 0) :
    Tendsto (fun j ↦ LeafCandidates.smoothRieszMeasure (v j) z r univ) atTop
      (𝓝 (μ (Metric.ball z r))) := by
  have heq (j : ℕ) : LeafCandidates.smoothRieszMeasure (v j) z r univ =
      smoothRieszOn U (v j) (Metric.ball z r) := by
    rw [← smoothRieszOn_restrict_ball (Metric.ball_subset_closedBall.trans hball),
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
  simpa only [heq] using smoothRieszOn_tendsto_ball hU hv hμ hvague z r hball hzero

/-- A strict limiting disc-mass bound persists for every sufficiently late
smooth measure, in the ENNReal convention consumed by the L08 decomposition. -/
theorem L08_eventually_mass_lt {U : Set ℂ} (hU : IsOpen U)
    {v : ℕ → ℂ → ℝ} {μ : Measure ℂ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤)
    (hvague : ∀ f : C_c(ℂ, ℝ), tsupport f ⊆ U →
      Tendsto (fun j ↦ ∫ z, f z ∂smoothRieszOn U (v j)) atTop (𝓝 (∫ z, f z ∂μ)))
    (z : ℂ) (r : ℝ) (hball : Metric.closedBall z r ⊆ U)
    (hzero : μ (Metric.sphere z r) = 0) {b : ENNReal} (hb : μ (Metric.ball z r) < b) :
    ∀ᶠ j in atTop, LeafCandidates.smoothRieszMeasure (v j) z r univ < b :=
  (L08_smoothRieszMeasure_tendsto_mass hU hv hμ hvague z r hball hzero).eventually_lt_const hb

end Yau.NodeProofs.D02RieszAux
