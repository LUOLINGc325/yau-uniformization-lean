import Yau.LeafProofs.L17LocalScalarAssemblyNear

open Set Metric
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def scalarAssemblyLocalBudget (Cw γ : ℝ) : ℝ := 1+Cw*(3 : ℝ)^(1-γ)+2*(2 : ℝ)^γ

theorem scalarAssemblyLocalBudget_nonneg {Cw γ : ℝ} (hCw : 0 ≤ Cw) :
    0 ≤ scalarAssemblyLocalBudget Cw γ := by unfold scalarAssemblyLocalBudget; positivity

theorem scalarScaledDistance_nonneg (P : UniformChartPartition g) {T : ℝ}
    (q r : ComplexVector n × Time T) : 0 ≤ localScaledDistance P.radius q r :=
  div_nonneg (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) P.radius_pos.le

theorem scalarScaledDistance_symm (ρ : ℝ) {T : ℝ} (q r : ComplexVector n × Time T) :
    localScaledDistance ρ q r=localScaledDistance ρ r q := by
  unfold localScaledDistance
  rw [norm_sub_rev,abs_sub_comm]

theorem weightedLocalFunction_far_distance (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q r : ComplexVector n × Time T)
    (hq : weightedLocalFunction P u p q ≠ 0) (hr : r.1 ∉ ball (0 : ComplexVector n) P.radius) :
    (1/2 : ℝ) ≤ localScaledDistance P.radius q r := by
  have hqnorm : ‖q.1‖ ≤ P.radius/2 := by
    simpa only [mem_closedBall,dist_zero_right] using weightedLocalFunction_nonzero_mem_half P u p hq
  have hrnorm : P.radius ≤ ‖r.1‖ := le_of_not_gt (by
    simpa only [mem_ball,dist_zero_right] using hr)
  have htri : ‖r.1‖ ≤ ‖q.1-r.1‖+‖q.1‖ := by
    simpa only [norm_sub_rev,add_comm] using norm_le_insert' r.1 q.1
  unfold localScaledDistance
  apply (le_div_iff₀ P.radius_pos).mpr
  linarith [Real.sqrt_nonneg |(q.2 : ℝ)-(r.2 : ℝ)|]

theorem weightedLocalFunction_difference_far (P : UniformChartPartition g) {T γ : ℝ}
    (hγ : 0 ≤ γ) (u : LocalHolderSpace ℝ P T γ) (p : P.centers)
    (q r : ComplexVector n × Time T) (hq : weightedLocalFunction P u p q ≠ 0)
    (hr : r.1 ∉ ball (0 : ComplexVector n) P.radius) :
    |weightedLocalFunction P u p q-weightedLocalFunction P u p r| ≤
      ((2*(2 : ℝ)^γ)*‖u‖)*(localScaledDistance P.radius q r)^γ := by
  have h := norm_sub_le_far_power
    (a := weightedLocalFunction P u p q) (b := weightedLocalFunction P u p r)
    (norm_nonneg u) (by norm_num : (0 : ℝ) < 1/2)
    (weightedLocalFunction_far_distance P u p q r hq hr) hγ
    (by simpa only [Real.norm_eq_abs] using weightedLocalFunction_abs_le P u p q)
    (by simpa only [Real.norm_eq_abs] using weightedLocalFunction_abs_le P u p r)
  simpa only [Real.norm_eq_abs,show ((1/2 : ℝ)⁻¹)=2 by norm_num,mul_assoc,mul_comm,mul_left_comm] using h

theorem weightedLocalFunction_difference (P : UniformChartPartition g) {T γ Cw : ℝ}
    (hTime : T ≤ P.radius^2) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hCw : 0 ≤ Cw)
    (hD : ∀ (p : P.centers) (q : M.Carrier) z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
      ‖fderiv ℝ (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ Cw/P.radius)
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q r : ComplexVector n × Time T) :
    |weightedLocalFunction P u p q-weightedLocalFunction P u p r| ≤
      (scalarAssemblyLocalBudget Cw γ*‖u‖)*(localScaledDistance P.radius q r)^γ := by
  have hp : 0 ≤ (localScaledDistance P.radius q r)^γ := Real.rpow_nonneg (scalarScaledDistance_nonneg P q r) _
  have hNear : (1+Cw*(3 : ℝ)^(1-γ))*‖u‖ ≤ scalarAssemblyLocalBudget Cw γ*‖u‖ :=
    mul_le_mul_of_nonneg_right (by
      unfold scalarAssemblyLocalBudget
      exact le_add_of_nonneg_right (by positivity)) (norm_nonneg u)
  have hFar : (2*(2 : ℝ)^γ)*‖u‖ ≤ scalarAssemblyLocalBudget Cw γ*‖u‖ :=
    mul_le_mul_of_nonneg_right (by
      unfold scalarAssemblyLocalBudget
      have h : 0 ≤ 1+Cw*(3 : ℝ)^(1-γ) := by positivity
      linarith) (norm_nonneg u)
  have hq0 (hz : q.1 ∉ ball (0 : ComplexVector n) P.radius) : weightedLocalFunction P u p q=0 := by
    simp only [weightedLocalFunction,dite_eq_right hz]
  have hr0 (hz : r.1 ∉ ball (0 : ComplexVector n) P.radius) : weightedLocalFunction P u p r=0 := by
    simp only [weightedLocalFunction,dite_eq_right hz]
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · by_cases hw : r.1 ∈ ball (0 : ComplexVector n) P.radius
    · exact (weightedLocalFunction_difference_inside P hTime hγ1 hCw hD u p
        (⟨q.1,hz⟩,q.2) (⟨r.1,hw⟩,r.2)).trans (mul_le_mul_of_nonneg_right hNear hp)
    · by_cases hzero : weightedLocalFunction P u p q=0
      · rw [hzero,hr0 hw,sub_self,abs_zero]
        exact mul_nonneg (mul_nonneg (scalarAssemblyLocalBudget_nonneg hCw) (norm_nonneg u)) hp
      · exact (weightedLocalFunction_difference_far P hγ0 u p q r hzero hw).trans
          (mul_le_mul_of_nonneg_right hFar hp)
  · by_cases hzero : weightedLocalFunction P u p r=0
    · rw [hq0 hz,hzero,sub_self,abs_zero]
      exact mul_nonneg (mul_nonneg (scalarAssemblyLocalBudget_nonneg hCw) (norm_nonneg u)) hp
    · have h := weightedLocalFunction_difference_far P hγ0 u p r q hzero hz
      rw [abs_sub_comm,scalarScaledDistance_symm P.radius r q] at h
      exact h.trans (mul_le_mul_of_nonneg_right hFar hp)

end Yau.LeafProofs.L17LocalScalarAssemblyAux
