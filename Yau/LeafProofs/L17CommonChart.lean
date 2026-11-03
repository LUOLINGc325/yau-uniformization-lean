import Yau.LeafProofs.L17InteriorCoordinates
import Yau.LeafProofs.L17UniformPartition

/-! Nearby actual points have a common selected chart with a uniform coordinate bound. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem UniformChartPartition.exists_common_chart_of_distance_lt
    (P : UniformChartPartition g) (hg : MetricSmooth g) (x y : M.Carrier)
    (hxy : inducedDistance g x y <
      Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 4)) :
    ∃ p : P.centers, ∃ z w : ComplexVector n,
      z ∈ ball 0 (P.radius / 4) ∧ w ∈ ball 0 P.radius ∧
      P.charts.chart p z = x ∧ P.charts.chart p w = y ∧
      ‖z - w‖ ≤ (Real.sqrt (2 * (P.charts.bound 0)⁻¹))⁻¹ * inducedDistance g x y := by
  obtain ⟨p, hp, z, hz, hzx⟩ := P.covers x
  let s : P.centers := ⟨p, hp⟩
  have hC := P.charts.bound_pos 0
  have hc : 0 < Real.sqrt (2 * (P.charts.bound 0)⁻¹) := by positivity
  have hhalf : 0 < P.radius / 2 := by have := P.radius_pos; positivity
  have hBG : closedBall z (P.radius / 2) ⊆ ball 0 P.charts.radius := by
    intro u hu
    apply mem_ball.mpr
    calc
      dist u 0 ≤ dist u z + dist z 0 := dist_triangle _ _ _
      _ < P.radius / 2 + P.radius / 4 := add_lt_add_of_le_of_lt
        (mem_closedBall.mp hu) (mem_ball.mp hz)
      _ < P.radius := by have := P.radius_pos; linarith
      _ < P.charts.radius := P.radius_lt
  have hbudget : inducedDistance g (P.charts.chart p z) y <
      Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 2) := by
    rw [hzx]
    exact hxy.trans (mul_lt_mul_of_pos_left (by have := P.radius_pos; linarith) hc)
  obtain ⟨w, hw, hwy⟩ := P.charts.chartBall_contains_distance_ball_from hg p y z hhalf hBG hbudget
  have hwρ : w ∈ ball 0 P.radius := by
    apply mem_ball.mpr
    calc
      dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ < P.radius / 2 + P.radius / 4 := add_lt_add (mem_ball.mp hw) (mem_ball.mp hz)
      _ < P.radius := by have := P.radius_pos; linarith
  have hws := P.charts.closedBall_source p (ball_subset_closedBall
    ((ball_subset_ball P.radius_lt.le) hwρ))
  have hinv : (P.charts.chart p).symm y = w := by
    rw [← hwy]
    exact (P.charts.chart p).left_inv hws
  have hcoord := P.charts.coordinate_diff_le_distance hg p y z hhalf hBG hbudget
  rw [hinv, hzx] at hcoord
  exact ⟨s, z, w, hz, hwρ, hzx, hwy, (norm_sub_rev z w).trans_le hcoord⟩

end Yau.LeafProofs.L17Aux
