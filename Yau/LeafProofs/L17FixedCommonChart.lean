import Yau.LeafProofs.L17CommonChart
import Yau.LeafProofs.L17TransitionJetOperator

/-! A fixed selected chart contains every image point of a sufficiently short coordinate segment. -/

noncomputable section

open Set Metric

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem UniformChartPartition.inverseChart_mem_of_distance_lt
    (P : UniformChartPartition g) (hg : MetricSmooth g) (p : P.centers)
    {z₀ : ComplexVector n} (hz₀ : z₀ ∈ ball 0 (P.radius / 4)) (y : M.Carrier)
    (hxy : inducedDistance g (P.charts.chart p z₀) y <
      Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 4)) :
    y ∈ (P.charts.chart p).target ∧
      (P.charts.chart p).symm y ∈ ball (0 : ComplexVector n) P.radius ∧
      ‖(P.charts.chart p).symm y - z₀‖ ≤
        (Real.sqrt (2 * (P.charts.bound 0)⁻¹))⁻¹ *
          inducedDistance g (P.charts.chart p z₀) y := by
  have hC := P.charts.bound_pos 0
  have hc : 0 < Real.sqrt (2 * (P.charts.bound 0)⁻¹) := by positivity
  have hhalf : 0 < P.radius / 2 := by have := P.radius_pos; positivity
  have hBG : closedBall z₀ (P.radius / 2) ⊆ ball 0 P.charts.radius := by
    intro u hu
    apply mem_ball.mpr
    calc
      dist u 0 ≤ dist u z₀ + dist z₀ 0 := dist_triangle _ _ _
      _ < P.radius / 2 + P.radius / 4 :=
        add_lt_add_of_le_of_lt (mem_closedBall.mp hu) (mem_ball.mp hz₀)
      _ < P.radius := by have := P.radius_pos; linarith
      _ < P.charts.radius := P.radius_lt
  have hbudget : inducedDistance g (P.charts.chart p z₀) y <
      Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 2) :=
    hxy.trans (mul_lt_mul_of_pos_left (by have := P.radius_pos; linarith) hc)
  obtain ⟨w, hw, hwy⟩ := P.charts.chartBall_contains_distance_ball_from hg p y z₀ hhalf hBG hbudget
  have hwρ : w ∈ ball (0 : ComplexVector n) P.radius := by
    apply mem_ball.mpr
    calc
      dist w 0 ≤ dist w z₀ + dist z₀ 0 := dist_triangle _ _ _
      _ < P.radius / 2 + P.radius / 4 := add_lt_add (mem_ball.mp hw) (mem_ball.mp hz₀)
      _ < P.radius := by have := P.radius_pos; linarith
  have hws := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hwρ))
  have hinv : (P.charts.chart p).symm y = w := by
    rw [← hwy]
    exact (P.charts.chart p).left_inv hws
  refine ⟨?_, by rw [hinv]; exact hwρ,
    P.charts.coordinate_diff_le_distance hg p y z₀ hhalf hBG hbudget⟩
  rw [← hwy]
  exact (P.charts.chart p).map_source hws

theorem UniformChartPartition.exists_chart_containing_segment
    (P : UniformChartPartition g) (hg : MetricSmooth g) (q : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball 0 P.radius) (hw : w ∈ ball 0 P.radius)
    (hshort : ‖w - z‖ < Real.sqrt (2 * (P.charts.bound 0)⁻¹) * P.radius /
        (4 * Real.sqrt (2 * P.charts.bound 0))) :
    ∃ p : P.centers,
      segment ℝ z w ⊆ P.charts.transitionBallDomain (q, p) ∧
      ∀ v ∈ segment ℝ z w,
        P.charts.transitionMap (q, p) v ∈ ball (0 : ComplexVector n) P.radius := by
  obtain ⟨p, hp, ξ, hξ, hξz⟩ := P.covers (P.charts.chart q z)
  let p' : P.centers := ⟨p, hp⟩
  have hC := P.charts.bound_pos 0
  have hcplus : 0 < Real.sqrt (2 * P.charts.bound 0) := by positivity
  have hsmall : Real.sqrt (2 * P.charts.bound 0) * ‖w - z‖ <
      Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 4) := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hcplus)).mp hshort
    nlinarith
  have hmaps (v : ComplexVector n) (hv : v ∈ segment ℝ z w) :
      P.charts.chart q v ∈ (P.charts.chart p).target ∧
        (P.charts.chart p).symm (P.charts.chart q v) ∈ ball (0 : ComplexVector n) P.radius := by
    have hvρ : v ∈ ball (0 : ComplexVector n) P.radius :=
      (convex_ball (0 : ComplexVector n) P.radius).segment_subset hz hw hv
    have hdist := P.charts.distance_le hg q ((ball_subset_ball P.radius_lt.le) hz)
      ((ball_subset_ball P.radius_lt.le) hvρ)
    rw [dist_eq_norm, norm_sub_rev z v] at hdist
    have hvz := norm_sub_le_of_mem_segment hv
    have hd : inducedDistance g (P.charts.chart p ξ) (P.charts.chart q v) <
        Real.sqrt (2 * (P.charts.bound 0)⁻¹) * (P.radius / 4) := by
      rw [hξz]
      exact (hdist.trans (mul_le_mul_of_nonneg_left hvz hcplus.le)).trans_lt hsmall
    have h := P.inverseChart_mem_of_distance_lt hg p' hξ (P.charts.chart q v) hd
    exact ⟨h.1, h.2.1⟩
  refine ⟨p', ?_, ?_⟩
  · intro v hv
    have hvρ := (convex_ball (0 : ComplexVector n) P.radius).segment_subset hz hw hv
    have hvr := (ball_subset_ball P.radius_lt.le) hvρ
    have ht := hmaps v hv
    refine ⟨hvr, ⟨P.charts.closedBall_source q (ball_subset_closedBall hvr), ht.1⟩, ?_⟩
    simp only [Set.mem_preimage]
    exact (ball_subset_ball P.radius_lt.le) ht.2
  · intro v hv
    exact (hmaps v hv).2

end Yau.LeafProofs.L17Aux
