import Yau.LeafProofs.L17LocalizedSchauderNearCover
import Yau.LeafProofs.L17ScaledTransitionJets

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scaled_transition_segment_of_left_in_cover (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius) (p : P.centers) (q : M.Carrier)
    {z w : ComplexVector n} (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hStart : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius)
    (hShort : ‖w-z‖ < Real.sqrt (2*(P.charts.bound 0)⁻¹)/(2*Real.sqrt (2*P.charts.bound 0))) :
    let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
    segment ℝ z w ⊆ P.charts.scaledTransitionDomain a ∧
      ∀ u ∈ segment ℝ z w, P.charts.scaledTransitionMap a u ∈ ball (0 : ComplexVector n) 2 := by
  have hScale (u : ComplexVector n) (hu : u ∈ ball 0 1) :
      P.radius • u ∈ ball (0 : ComplexVector n) P.radius := by
    apply mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
    have hn : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
    simpa only [mul_one] using mul_lt_mul_of_pos_left hn P.radius_pos
  have hBudget : ‖P.radius • w-P.radius • z‖ <
      Real.sqrt (2*(P.charts.bound 0)⁻¹)*P.radius/(2*Real.sqrt (2*P.charts.bound 0)) := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
    exact (mul_lt_mul_of_pos_left hShort P.radius_pos).trans_eq (by ring)
  obtain ⟨hDomain,hTarget⟩ := transition_segment_of_left_in_cover P hg hρr p q
    (hScale z hz) (hScale w hw) hStart hBudget
  have hSegment (u : ComplexVector n) (hu : u ∈ segment ℝ z w) :
      P.radius • u ∈ segment ℝ (P.radius • z) (P.radius • w) := by
    let L : ComplexVector n →ₗ[ℝ] ComplexVector n := P.radius • LinearMap.id
    have hh : L.toAffineMap u ∈ L.toAffineMap '' segment ℝ z w := ⟨u,hu,rfl⟩
    rw [image_segment] at hh
    exact hh
  let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
  have hTargetUnit (u : ComplexVector n) (hu : u ∈ segment ℝ z w) :
      P.charts.scaledTransitionMap a u ∈ ball (0 : ComplexVector n) 2 := by
    have h := hTarget (P.radius • u) (hSegment u hu)
    change P.radius⁻¹ • P.charts.transitionMap (q,(p : M.Carrier)) (P.radius • u) ∈ ball 0 2
    apply mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr P.radius_pos)]
    have hn : ‖P.charts.transitionMap (q,(p : M.Carrier)) (P.radius • u)‖ < 2*P.radius := by
      simpa only [mem_ball,dist_zero_right] using h
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ P.radius_pos).mpr hn
  refine ⟨?_,hTargetUnit⟩
  intro u hu
  change P.radius • u ∈ P.charts.transitionBallDomain (q,(p : M.Carrier)) ∧
    P.charts.scaledTransitionMap a u ∈ ball (0 : ComplexVector n) 2
  exact ⟨hDomain (hSegment u hu),hTargetUnit u hu⟩

end Yau.LeafProofs.L17LocalizedSchauderAux
