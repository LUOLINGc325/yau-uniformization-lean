import Yau.LeafProofs.L17LocalizedSchauderRawTransport
import Yau.LeafProofs.L17LocalizedSchauderFamilyBounds

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem rawLocalizedTerm_unit_eq_of_domain (P : UniformChartPartition g) (hρone : P.radius ≤ 1)
    {T : ℝ} (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ)
    (hvZero : ∀ z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v (z,t) = 0)
    (t : Time T) {z : ComplexVector n}
    (hz : z ∈ P.charts.scaledTransitionDomain (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))) :
    rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t) =
      v (P.radius • P.charts.scaledTransitionMap (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier))) z,t) := by
  have hTarget : P.charts.chart q (P.radius • z) ∈ (P.charts.chart p).target := hz.1.2.1.2
  rw [rawLocalizedTerm_eq_of_target P T p v hvZero (P.charts.chart q (P.radius • z),t) hTarget]
  simp only [BoundedChartFamily.scaledTransitionMap,BoundedChartFamily.transitionMap,
    smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul]

theorem rawLocalizedTerm_near_left (P : UniformChartPartition g) (hg : MetricSmooth g)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius)
    {T : ℝ} (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ)
    (hvZero : ∀ z, z ∉ closedBall (0 : ComplexVector n) P.radius → ∀ t, v (z,t) = 0)
    {B D gamma : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hγ : 0 ≤ gamma)
    (hHolder : ∀ z w, z ∈ ball (0 : ComplexVector n) (2*P.radius) → w ∈ ball 0 (2*P.radius) →
      ∀ t s : Time T, |v (z,t)-v (w,s)| ≤ B*(localScaledDistance P.radius (z,t) (w,s))^gamma)
    (hTransition : TransitionJetBounds P.charts 0 D)
    (t s : Time T) {z w : ComplexVector n} (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hx : P.charts.chart q (P.radius • z) ∈ P.charts.chart p '' closedBall 0 P.radius)
    (hNear : unitParabolicDistance P.radius (z,t) (w,s) < nearCoverRadius P.charts) :
    |rawLocalizedTerm P T p v (P.charts.chart q (P.radius • z),t)-
      rawLocalizedTerm P T p v (P.charts.chart q (P.radius • w),s)| ≤
      D^gamma*B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
  let τ := P.charts.scaledTransitionMap a
  have hSpace := unitParabolicDistance_space_le P.radius_pos (z,t) (w,s)
  obtain ⟨hSegment,hTarget⟩ := scaled_transition_segment_of_left_in_cover P hg hρone hρr p q hz hw hx
    (by rw [norm_sub_rev]; exact hSpace.trans_lt (hNear.trans_le (min_le_right _ _)))
  have hzDom := hSegment (left_mem_segment ℝ z w)
  have hwDom := hSegment (right_mem_segment ℝ z w)
  have hzTarget := hTarget z (left_mem_segment ℝ z w)
  have hwTarget := hTarget w (right_mem_segment ℝ z w)
  have hLip : ‖τ z-τ w‖ ≤ D*‖z-w‖ :=
    scaled_transition_value_lipschitz P.charts a (hTransition.2 a z w hSegment 0 (by omega))
  have hPower := unitParabolicDistance_map_rpow_le P.radius_pos hD hγ τ (z,t) (w,s) hLip
  rw [rawLocalizedTerm_unit_eq_of_domain P hρone p q v hvZero t hzDom,
    rawLocalizedTerm_unit_eq_of_domain P hρone p q v hvZero s hwDom]
  have h := hHolder (P.radius • τ z) (P.radius • τ w)
    (radius_smul_mem_ball_two P hzTarget) (radius_smul_mem_ball_two P hwTarget) t s
  rw [localScaledDistance_radius_eq P.radius_pos] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hPower hB).trans_eq (by ring))

end Yau.LeafProofs.L17LocalizedSchauderAux
