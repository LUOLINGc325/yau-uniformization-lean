import spec.CHAIN.CONTRACTS

/-! V01 scratch source: a genuine compact space-time cylinder is chosen
inside a supplied neighborhood of the original contact point. -/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Yau.Blueprint.V01Proof

theorem exists_compact_cylinder_subset_nhds
    {E : Type*} [MetricSpace E] [ProperSpace E]
    (z : E) (s : ℝ) {V : Set (E × ℝ)} (hV : V ∈ 𝓝 (z, s)) :
    ∃ r : ℝ, 0 < r ∧
      IsCompact (closedBall z r ×ˢ Icc (s - r) (s + r)) ∧
      (z, s) ∈ interior (closedBall z r ×ˢ Icc (s - r) (s + r)) ∧
      closedBall z r ×ˢ Icc (s - r) (s + r) ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε
  refine ⟨r, hr, (isCompact_closedBall z r).prod isCompact_Icc, ?_, ?_⟩
  · apply mem_interior_iff_mem_nhds.mpr
    exact prod_mem_nhds (closedBall_mem_nhds z hr)
      (Icc_mem_nhds (by linarith) (by linarith))
  · rintro ⟨y, t⟩ ⟨hy, ht⟩
    apply hball
    apply Metric.mem_ball.mpr
    have hyd : dist y z ≤ r := Metric.mem_closedBall.mp hy
    have htd : dist t s ≤ r := by
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (max_le hyd htd).trans_lt hrε

end Yau.Blueprint.V01Proof
