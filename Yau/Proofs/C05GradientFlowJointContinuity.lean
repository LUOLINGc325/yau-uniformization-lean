import Yau.Proofs.C05GradientFlowGeodesic

/-! Time continuity and spatial nonexpansion give joint continuity on the trapping set. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem joint_continuousOn_of_time_continuous_nonexpansive
    (g : SmoothMetric M) (F : ℝ → M.Carrier → M.Carrier) (K : Set M.Carrier)
    (htime : ∀ x ∈ K, ContinuousOn (fun t => F t x) (Set.Ici (0 : ℝ)))
    (hspace : ∀ t, 0 ≤ t → ∀ x ∈ K, ∀ y ∈ K,
      inducedDistance g.form (F t x) (F t y) ≤ inducedDistance g.form x y) :
    ContinuousOn (fun p : ℝ × M.Carrier => F p.1 p.2) (Set.Ici 0 ×ˢ K) := by
  letI := inducedMetricSpace g
  intro p hp
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, htimeδ⟩ := Metric.continuousWithinAt_iff.mp
    (htime p.2 hp.2 p.1 hp.1) (ε / 2) (by positivity)
  refine ⟨min δ (ε / 2), lt_min hδ (by positivity), ?_⟩
  intro q hq hqp
  have hqt : dist q.1 p.1 < δ := by
    have H : dist q.1 p.1 ≤ dist q p := by simp only [Prod.dist_eq]; exact le_max_left _ _
    exact H.trans_lt (hqp.trans_le (min_le_left _ _))
  have hqx : dist q.2 p.2 < ε / 2 := by
    have H : dist q.2 p.2 ≤ dist q p := by simp only [Prod.dist_eq]; exact le_max_right _ _
    exact H.trans_lt (hqp.trans_le (min_le_right _ _))
  have Htime := htimeδ hq.1 hqt
  have Hspace := hspace q.1 hq.1 q.2 hq.2 p.2 hp.2
  change dist (F q.1 q.2) (F q.1 p.2) ≤ dist q.2 p.2 at Hspace
  exact (dist_triangle (F q.1 q.2) (F q.1 p.2) (F p.1 p.2)).trans_lt
    (by linarith)

end Yau.Proofs.C05GradientFlowAux
