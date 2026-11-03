import Yau.Proofs.F01AtlasLimitScalarSmooth

/-! Joint smoothness in the actual small bounded charts implies the
original manifold space-time smoothness on the same time set. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_of_bounded_atlas_coefficients
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {r : ℝ} (hr : 0 < r) (hrA : r ≤ A.radius)
    (U : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (hU : ∀ a, ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => U (A.chart a p.1) p.2)
      (ball 0 r ×ˢ I)) : SmoothSpaceTime U I := by
  obtain ⟨P, hPA, _⟩ := (shrunkBoundedChartFamily A r hr hrA).exists_uniform_partition_below hg hr
  have hPr : P.radius < r := by simpa only [hPA, shrunkBoundedChartFamily] using P.radius_lt
  apply Yau.LeafProofs.L17BootstrapSmoothAux.smoothSpaceTime_of_local_background_charts P
  intro y
  obtain ⟨p, hp, z, hz, hzy⟩ := P.covers y
  have hzP : z ∈ ball 0 P.radius := ball_subset_ball (by linarith [P.radius_pos]) hz
  have hzr : z ∈ ball 0 r := ball_subset_ball (by linarith [P.radius_pos]) hz
  obtain ⟨d, hd, hBall⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzr)
  refine ⟨⟨p, hp⟩, z, d, hd, hzP, hzy, ?_⟩
  have hCoeff : ContDiffOn ℝ ∞
      (fun q : ComplexVector n × ℝ => U (P.charts.chart p q.1) q.2) (ball 0 r ×ˢ I) := by
    simpa only [hPA, shrunkBoundedChartFamily] using hU p
  exact hCoeff.mono (prod_mono hBall Subset.rfl)

end Yau.NodeProofs.F01Aux
