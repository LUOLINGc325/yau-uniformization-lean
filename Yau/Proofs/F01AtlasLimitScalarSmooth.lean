import Yau.Proofs.F01ShrunkChartFamily
import Yau.Proofs.F01SpaceTimeChart
import Yau.LeafProofs.L17BootstrapScalarSmooth

/-! Smooth scalar coefficients in the actual small bounded charts
give native smoothness via the existing transition theorem and an
actual uniform subcover. -/
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothFn_of_bounded_atlas_coefficients
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {r : ℝ} (hr : 0 < r) (hrA : r ≤ A.radius) (u : M.Carrier → ℝ)
    (hu : ∀ a, ContDiffOn ℝ ∞ (fun z => u ((A.chart a) z)) (ball 0 r)) : SmoothFn u := by
  obtain ⟨P, hPA, _⟩ := (shrunkBoundedChartFamily A r hr hrA).exists_uniform_partition_below hg hr
  have hPr : P.radius < r := by simpa only [hPA, shrunkBoundedChartFamily] using P.radius_lt
  have hFamily : SmoothSpaceTime (fun x (_ : ℝ) => u x) univ := by
    apply Yau.LeafProofs.L17BootstrapSmoothAux.smoothSpaceTime_of_local_background_charts P
    intro y
    obtain ⟨p, hp, z, hz, hzy⟩ := P.covers y
    have hzP : z ∈ ball 0 P.radius := ball_subset_ball (by linarith [P.radius_pos]) hz
    have hzr : z ∈ ball 0 r := ball_subset_ball (by linarith [P.radius_pos]) hz
    obtain ⟨d, hd, hBall⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzr)
    refine ⟨⟨p, hp⟩, z, d, hd, hzP, hzy, ?_⟩
    have hCoeff : ContDiffOn ℝ ∞ (fun w => u ((P.charts.chart p) w)) (ball 0 r) := by
      simpa only [hPA, shrunkBoundedChartFamily] using hu p
    exact (hCoeff.mono hBall).comp contDiffOn_fst (fun q hq => hq.1)
  exact smoothSpaceTime_slice hFamily (mem_univ (0 : ℝ))

end Yau.NodeProofs.F01Aux
