import Yau.LeafProofs.L17LocalizedSchauderUniformTransport

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem inv_radius_smul_mem_unit_ball (P : UniformChartPartition g) {z : ComplexVector n}
    (hz : z ∈ ball 0 P.radius) : P.radius⁻¹ • z ∈ ball (0 : ComplexVector n) 1 := by
  apply mem_ball.mpr
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr P.radius_pos)]
  rw [← div_eq_inv_mul]
  exact (div_lt_one P.radius_pos).mpr (by simpa only [mem_ball,dist_zero_right] using hz)

theorem unitParabolicDistance_inv_radius (P : UniformChartPartition g) {T : ℝ}
    (q r : ChartCylinder P T) :
    unitParabolicDistance P.radius (P.radius⁻¹ • (q.1 : ComplexVector n),q.2)
      (P.radius⁻¹ • (r.1 : ComplexVector n),r.2) = parabolicDistance q r/P.radius := by
  unfold unitParabolicDistance parabolicDistance
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr P.radius_pos)]
  ring

theorem pairWeight_mul_scaled_power (P : UniformChartPartition g) (T gamma : ℝ)
    (i : ChartPairs P T) :
    pairWeight P T gamma i*(parabolicDistance i.2.val.1 i.2.val.2/P.radius)^gamma = 1 := by
  have hD := parabolicDistance_pos_of_ne i.2.property
  unfold pairWeight scaledPairWeight
  rw [Real.div_rpow hD.le P.radius_pos.le]
  field_simp [(Real.rpow_pos_of_pos hD gamma).ne',(Real.rpow_pos_of_pos P.radius_pos gamma).ne']

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_weighted_pair_le (P : UniformChartPartition g) (T gamma : ℝ)
    (i : ChartPairs P T) (a b : F) {B : ℝ}
    (h : ‖a-b‖ ≤ B*(parabolicDistance i.2.val.1 i.2.val.2/P.radius)^gamma) :
    ‖pairWeight P T gamma i • (a-b)‖ ≤ B := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (pairWeight_pos P T gamma i)]
  calc
    _ ≤ pairWeight P T gamma i*(B*(parabolicDistance i.2.val.1 i.2.val.2/P.radius)^gamma) :=
      mul_le_mul_of_nonneg_left h (pairWeight_pos P T gamma i).le
    _ = B := by rw [mul_left_comm,pairWeight_mul_scaled_power,mul_one]

end Yau.LeafProofs.L17LocalizedSchauderAux
