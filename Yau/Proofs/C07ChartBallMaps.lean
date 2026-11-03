import Yau.Proofs.D04AtlasGlueCover

/-! Center the accepted nested coordinate balls without changing their original manifold chart. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set
open Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {M : ComplexManifold n}

def chartBallMap (B : ChartBall M) (w : ComplexVector n) : M.Carrier :=
  chartInv B.center (w + chartPt B.center B.center)

def chartBallCoord (B : ChartBall M) (x : M.Carrier) : ComplexVector n :=
  chartPt B.center x - chartPt B.center B.center

theorem chartBallMap_zero (B : ChartBall M) : chartBallMap B 0 = B.center := by
  simp only [chartBallMap, zero_add]
  exact (extChartAt (ComplexModel n) B.center).left_inv (mem_extChartAt_source B.center)

theorem chartBall_shift_mem_target (B : ChartBall M) {w : ComplexVector n}
    (hw : ‖w‖ ≤ 3 * B.radius) : w + chartPt B.center B.center ∈ chartTarget B.center := by
  apply B.closed_triple_subset
  simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right] using hw

theorem chartBallMap_contMDiff (B : ChartBall M) :
    ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ (chartBallMap B)
      (Metric.ball 0 (3 * B.radius)) := by
  let q : ComplexVector n → ComplexVector n := fun w => w + chartPt B.center B.center
  have hq : ContMDiff 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n) ∞ q :=
    (contDiff_id.add contDiff_const).contMDiff
  have hmaps : MapsTo q (Metric.ball 0 (3 * B.radius)) (chartTarget B.center) := by
    intro w hw
    apply chartBall_shift_mem_target B
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  change ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
    ((extChartAt (ComplexModel n) B.center).symm ∘ q) (Metric.ball 0 (3 * B.radius))
  exact (contMDiffOn_extChartAt_symm (I := ComplexModel n) (n := ∞) B.center).comp hq.contMDiffOn hmaps

theorem chartBall_image_ball (B : ChartBall M) (q : ℝ) :
    chartInv B.center '' Metric.ball (chartPt B.center B.center) q =
      chartBallMap B '' Metric.ball 0 q := by
  apply Set.Subset.antisymm
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨w - chartPt B.center B.center, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hw
    · simp only [chartBallMap, sub_add_cancel]
  · rintro x ⟨w, hw, rfl⟩
    refine ⟨w + chartPt B.center B.center, ?_, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw

theorem chartBall_outer_subset_source (B : ChartBall M) :
    B.outer ⊆ (extChartAt (ComplexModel n) B.center).source := by
  rintro x ⟨w, hw, rfl⟩
  exact (extChartAt (ComplexModel n) B.center).map_target (B.outer_subset_target hw)

theorem chartBallCoord_outer (B : ChartBall M) {x : M.Carrier} (hx : x ∈ B.outer) :
    chartBallCoord B x ∈ Metric.ball 0 (2 * B.radius) := by
  obtain ⟨w, hw, rfl⟩ := hx
  simp only [chartBallCoord, Metric.mem_ball, dist_zero_right]
  have hround : chartPt B.center (chartInv B.center w) = w :=
    (extChartAt (ComplexModel n) B.center).right_inv (B.outer_subset_target hw)
  rw [hround]
  simpa only [Metric.mem_ball, dist_eq_norm] using hw

theorem chartBallMap_coord (B : ChartBall M) {x : M.Carrier} (hx : x ∈ B.outer) :
    chartBallMap B (chartBallCoord B x) = x := by
  simp only [chartBallMap, chartBallCoord, sub_add_cancel]
  exact (extChartAt (ComplexModel n) B.center).left_inv (chartBall_outer_subset_source B hx)

theorem chartBallCoord_continuousOn (B : ChartBall M) :
    ContinuousOn (chartBallCoord B) B.outer := by
  have hsource : B.outer ⊆ (chartAt (ComplexVector n) B.center).source := by
    simpa only [extChartAt_source] using chartBall_outer_subset_source B
  have hc : ContinuousOn (chartPt B.center) B.outer :=
    (contMDiffOn_extChartAt (I := ComplexModel n) (n := ∞) (x := B.center)).continuousOn.mono
      hsource
  exact hc.sub continuousOn_const

theorem chartBall_inner_preconnected (B : ChartBall M) : IsPreconnected B.inner := by
  rw [ChartBall.inner, chartBall_image_ball]
  exact (convex_ball (0 : ComplexVector n) B.radius).isPreconnected.image _
    ((chartBallMap_contMDiff B).continuousOn.mono
      (Metric.ball_subset_ball (by linarith [B.radius_pos])))

theorem chartBall_outer_preconnected (B : ChartBall M) : IsPreconnected B.outer := by
  rw [ChartBall.outer, chartBall_image_ball]
  exact (convex_ball (0 : ComplexVector n) (2 * B.radius)).isPreconnected.image _
    ((chartBallMap_contMDiff B).continuousOn.mono
      (Metric.ball_subset_ball (by linarith [B.radius_pos])))

theorem chartBallMap_compact_outer (B : ChartBall M) :
    IsCompact (chartBallMap B '' Metric.closedBall 0 (2 * B.radius)) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartBallMap_contMDiff B).continuousOn.mono
      (Metric.closedBall_subset_ball (by linarith [B.radius_pos])))

end Yau.Proofs.C07Aux
