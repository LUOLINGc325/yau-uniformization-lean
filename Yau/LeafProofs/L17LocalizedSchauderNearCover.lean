import Yau.LeafProofs.L17LocalizedSchauderSpatialTransport
import Yau.LeafProofs.L17FixedCommonChart

open Set Metric
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem inverseChart_mem_two_of_active_distance (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρr : 2*P.radius < P.charts.radius) (p : P.centers)
    {ξ : ComplexVector n} (hξ : ξ ∈ closedBall 0 P.radius) (y : M.Carrier)
    (hNear : inducedDistance g (P.charts.chart p ξ) y <
      Real.sqrt (2*(P.charts.bound 0)⁻¹)*(P.radius/2)) :
    y ∈ (P.charts.chart p).target ∧
      (P.charts.chart p).symm y ∈ ball (0 : ComplexVector n) (2*P.radius) ∧
      ‖(P.charts.chart p).symm y-ξ‖ ≤ (Real.sqrt (2*(P.charts.bound 0)⁻¹))⁻¹*
        inducedDistance g (P.charts.chart p ξ) y := by
  have hR : 0 < P.radius/2 := by have := P.radius_pos; positivity
  have hBG : closedBall ξ (P.radius/2) ⊆ ball (0 : ComplexVector n) P.charts.radius := by
    intro u hu
    apply mem_ball.mpr
    calc
      dist u 0 ≤ dist u ξ+dist ξ 0 := dist_triangle _ _ _
      _ ≤ P.radius/2+P.radius := add_le_add (mem_closedBall.mp hu) (mem_closedBall.mp hξ)
      _ < 2*P.radius := by have := P.radius_pos; linarith
      _ < P.charts.radius := hρr
  obtain ⟨w,hw,hwy⟩ := P.charts.chartBall_contains_distance_ball_from hg p y ξ hR hBG hNear
  have hw2 : w ∈ ball (0 : ComplexVector n) (2*P.radius) := by
    apply mem_ball.mpr
    calc
      dist w 0 ≤ dist w ξ+dist ξ 0 := dist_triangle _ _ _
      _ < P.radius/2+P.radius := add_lt_add_of_lt_of_le (mem_ball.mp hw) (mem_closedBall.mp hξ)
      _ < 2*P.radius := by have := P.radius_pos; linarith
  have hws := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball hρr.le) hw2))
  have hinv : (P.charts.chart p).symm y = w := by rw [← hwy]; exact (P.charts.chart p).left_inv hws
  refine ⟨?_,by rw [hinv]; exact hw2,
    P.charts.coordinate_diff_le_distance hg p y ξ hR hBG hNear⟩
  rw [← hwy]
  exact (P.charts.chart p).map_source hws

theorem transition_segment_of_left_in_cover (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρr : 2*P.radius < P.charts.radius) (p : P.centers) (q : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball 0 P.radius) (hw : w ∈ ball 0 P.radius)
    (hStart : P.charts.chart q z ∈ P.charts.chart p '' closedBall 0 P.radius)
    (hShort : ‖w-z‖ < Real.sqrt (2*(P.charts.bound 0)⁻¹)*P.radius/
      (2*Real.sqrt (2*P.charts.bound 0))) :
    segment ℝ z w ⊆ P.charts.transitionBallDomain (q,(p : M.Carrier)) ∧
      ∀ u ∈ segment ℝ z w,
        P.charts.transitionMap (q,(p : M.Carrier)) u ∈ ball (0 : ComplexVector n) (2*P.radius) := by
  obtain ⟨ξ,hξ,hξz⟩ := hStart
  have hC := P.charts.bound_pos 0
  have hc : 0 < Real.sqrt (2*P.charts.bound 0) := by positivity
  have hSmall : Real.sqrt (2*P.charts.bound 0)*‖w-z‖ <
      Real.sqrt (2*(P.charts.bound 0)⁻¹)*(P.radius/2) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).mp hShort
    nlinarith
  have hMaps (u : ComplexVector n) (hu : u ∈ segment ℝ z w) :
      P.charts.chart q u ∈ (P.charts.chart p).target ∧
        P.charts.transitionMap (q,(p : M.Carrier)) u ∈ ball (0 : ComplexVector n) (2*P.radius) := by
    have huρ := (convex_ball (0 : ComplexVector n) P.radius).segment_subset hz hw hu
    have hDist := P.charts.distance_le hg q ((ball_subset_ball P.radius_lt.le) hz)
      ((ball_subset_ball P.radius_lt.le) huρ)
    rw [dist_eq_norm,norm_sub_rev z u] at hDist
    have hBudget : inducedDistance g (P.charts.chart p ξ) (P.charts.chart q u) <
        Real.sqrt (2*(P.charts.bound 0)⁻¹)*(P.radius/2) := by
      rw [hξz]
      exact (hDist.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hu) hc.le)).trans_lt hSmall
    have h := inverseChart_mem_two_of_active_distance P hg hρr p hξ (P.charts.chart q u) hBudget
    exact ⟨h.1,h.2.1⟩
  refine ⟨?_,fun u hu => (hMaps u hu).2⟩
  intro u hu
  have huρ := (convex_ball (0 : ComplexVector n) P.radius).segment_subset hz hw hu
  have hTarget := hMaps u hu
  change u ∈ ball (0 : ComplexVector n) P.charts.radius ∧
    (u ∈ (P.charts.chart q).source ∧ P.charts.chart q u ∈ (P.charts.chart p).target) ∧
      P.charts.transitionMap (q,(p : M.Carrier)) u ∈ ball (0 : ComplexVector n) P.charts.radius
  refine ⟨(ball_subset_ball P.radius_lt.le) huρ,
    ⟨P.charts.closedBall_source q (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) huρ)),hTarget.1⟩,?_⟩
  exact (ball_subset_ball hρr.le) hTarget.2

end Yau.LeafProofs.L17LocalizedSchauderAux
