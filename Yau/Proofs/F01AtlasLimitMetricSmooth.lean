import Yau.Proofs.F01ShrunkChartFamily
import Yau.Proofs.F01MetricFamilySlices
import Yau.LeafProofs.L17BootstrapMetricSmooth

/-! Smooth actual coefficients in the small original bounded charts
give native metric smoothness. The existing chart-transition theorem
is reused with a genuinely constructed uniform subcover. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricSmooth_of_bounded_atlas_coefficients
    (g K : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {r : ℝ} (hr : 0 < r) (hrA : r ≤ A.radius)
    (hK : ∀ a i j, ContDiffOn ℝ ∞
      (fun z => pullbackMatrix K (A.chart a) z i j) (ball 0 r)) : MetricSmooth K := by
  obtain ⟨P, hPA, _⟩ := (shrunkBoundedChartFamily A r hr hrA).exists_uniform_partition_below hg hr
  have hPr : P.radius < r := by simpa only [hPA, shrunkBoundedChartFamily] using P.radius_lt
  have hFamily : MetricFamilySmooth (fun _ : ℝ => K) univ := by
    apply Yau.LeafProofs.L17BootstrapMetricSmoothAux.metricFamilySmooth_of_local_pullback P
    intro y
    obtain ⟨p, hp, z, hz, hzy⟩ := P.covers y
    have hzP : z ∈ ball 0 P.radius := ball_subset_ball (by linarith [P.radius_pos]) hz
    have hzr : z ∈ ball 0 r := ball_subset_ball (by linarith [P.radius_pos]) hz
    obtain ⟨d, hd, hBall⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzr)
    refine ⟨⟨p, hp⟩, z, d, hd, hzP, hzy, ?_⟩
    intro i j
    have hCoeff : ContDiffOn ℝ ∞
        (fun w => pullbackMatrix K (P.charts.chart p) w i j) (ball 0 r) := by
      simpa only [hPA, shrunkBoundedChartFamily] using hK p i j
    exact (hCoeff.mono hBall).comp contDiffOn_fst (fun q hq => hq.1)
  exact metricFamilySmooth_slice hFamily (mem_univ (0 : ℝ))

end Yau.NodeProofs.F01Aux
