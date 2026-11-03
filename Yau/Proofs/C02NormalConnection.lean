import Yau.Proofs.C02ConnectionChartChange

/-! A global smooth connection field for the actual radial parallel gauge.
Chart independence permits choosing a target chart separately at each point
without making any smoothness assumption on that choice. -/

noncomputable section
open Set Filter
open scoped Manifold InnerProductSpace ContDiff Topology
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def normalConnection (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (x : ComplexVector n) : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  normalConnectionInChart g p U hU (normalRealMap g p U x) x

theorem normalConnection_eq_chart (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalConnection g p U hU x = normalConnectionInChart g p U hU c x :=
  normalConnectionInChart_chartChange g p U hU (normalRealMap g p U x) c x
    (mem_chart_source _ _) hx

theorem normalConnection_smooth (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) :
    ContDiff ℝ ∞ (normalConnection g p U hU) := by
  letI := manifold_realSmooth M
  rw [contDiff_iff_contDiffAt]
  intro x
  let c := normalRealMap g p U x
  have hO := (normalRealMap_smooth g p U hU).continuous.continuousAt.preimage_mem_nhds
    ((chartAt (ComplexVector n) c).open_source.mem_nhds (mem_chart_source _ _))
  have heq : normalConnection g p U hU =ᶠ[𝓝 x] normalConnectionInChart g p U hU c := by
    filter_upwards [hO] with y hy
    exact normalConnection_eq_chart g p U hU c y hy
  exact ((normalConnectionInChart_smooth g p U hU c).contDiffAt hO).congr_of_eventuallyEq heq

end Yau.Blueprint.C02Proof
