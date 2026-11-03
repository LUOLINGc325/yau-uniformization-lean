import Yau.Proofs.P03CompactChartCover

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- A countable atlas of actual compact coordinate balls, together with
the source and open-ball membership used by intrinsic section reconstruction. -/
theorem exists_countable_section_array_atlas {n : ℕ} (M : ComplexManifold n) :
    ∃ (T : Set M.Carrier), T.Countable ∧ ∃ r : T → ℝ,
      (∀ i, 0 < r i) ∧
      (∀ i, Metric.closedBall (chartPt i.1 i.1) (r i) ⊆ chartTarget i.1) ∧
      ∀ x : M.Carrier, ∃ i : T,
        x ∈ (extChartAt (ComplexModel n) i.1).source ∧
        chartPt i.1 x ∈ Metric.ball (chartPt i.1 i.1) (r i) := by
  classical
  obtain ⟨r, T, hr, hsub, hT, hcover⟩ := exists_countable_compact_chart_cover M
  refine ⟨T, hT, fun i => r i.1, (fun i => hr i.1), (fun i => hsub i.1), ?_⟩
  intro x
  have hx : x ∈ ⋃ a ∈ T, chartInv a '' Metric.ball (chartPt a a) (r a) := by
    rw [hcover]
    trivial
  obtain ⟨a, hx⟩ := mem_iUnion.mp hx
  obtain ⟨ha, hx⟩ := mem_iUnion.mp hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzt := hsub a (Metric.ball_subset_closedBall hz)
  refine ⟨⟨a, ha⟩, (extChartAt (ComplexModel n) a).map_target hzt, ?_⟩
  change (extChartAt (ComplexModel n) a)
    ((extChartAt (ComplexModel n) a).symm z) ∈ Metric.ball (chartPt a a) (r a)
  rw [(extChartAt (ComplexModel n) a).right_inv hzt]
  exact hz

end Yau.NodeProofs.P03Aux
