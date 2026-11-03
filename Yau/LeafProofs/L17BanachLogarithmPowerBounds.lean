import Yau.LeafProofs.L17BanachLogarithmSeries

noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.LeafProofs.L17BanachLogarithmAux

variable {A : Type*} [NormedRing A]

theorem norm_pow_succ_le_radius {r : ℝ} (hr : 0 ≤ r) {z : A} (hz : ‖z‖ ≤ r)
    (k : ℕ) : ‖z^(k+1)‖ ≤ r^(k+1) := by
  induction k with
  | zero => simpa only [zero_add,pow_one] using hz
  | succ k ih =>
    calc
      ‖z^(k+1+1)‖ = ‖z^(k+1)*z‖ := by rw [pow_succ]
      _ ≤ ‖z^(k+1)‖*‖z‖ := norm_mul_le _ _
      _ ≤ r^(k+1)*r := mul_le_mul ih hz (norm_nonneg _) (pow_nonneg hr _)
      _ = r^(k+1+1) := (pow_succ _ _).symm

theorem norm_pow_succ_sub_le_radius {r : ℝ} (hr : 0 ≤ r) {z w : A}
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (k : ℕ) :
    ‖z^(k+1)-w^(k+1)‖ ≤ ((k+1 : ℕ) : ℝ)*r^k*‖z-w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hid : z^(k+1+1)-w^(k+1+1)=z^(k+1)*(z-w)+(z^(k+1)-w^(k+1))*w := by
      simp only [pow_succ]
      noncomm_ring
    rw [hid]
    calc
      ‖z^(k+1)*(z-w)+(z^(k+1)-w^(k+1))*w‖
          ≤ ‖z^(k+1)*(z-w)‖+‖(z^(k+1)-w^(k+1))*w‖ := norm_add_le _ _
      _ ≤ ‖z^(k+1)‖*‖z-w‖+‖z^(k+1)-w^(k+1)‖*‖w‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ r^(k+1)*‖z-w‖+(((k+1 : ℕ) : ℝ)*r^k*‖z-w‖)*r :=
        add_le_add (mul_le_mul_of_nonneg_right (norm_pow_succ_le_radius hr hz k) (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (by positivity))
      _ = ((k+1+1 : ℕ) : ℝ)*r^(k+1)*‖z-w‖ := by
        rw [pow_succ]
        push_cast
        ring

variable [NormedAlgebra ℝ A]

theorem log_tail_term_sub_norm_le {r : ℝ} (hr : 0 ≤ r) {z w : A}
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (k : ℕ) :
    ‖logCoefficient (k+2) • z^(k+2)-logCoefficient (k+2) • w^(k+2)‖
      ≤ r^(k+1)*‖z-w‖ := by
  rw [← smul_sub,norm_smul,logCoefficient_norm (by omega)]
  calc
    1/((k+2 : ℕ) : ℝ)*‖z^(k+2)-w^(k+2)‖
        ≤ 1/((k+2 : ℕ) : ℝ)*(((k+2 : ℕ) : ℝ)*r^(k+1)*‖z-w‖) :=
      mul_le_mul_of_nonneg_left (norm_pow_succ_sub_le_radius hr hz hw (k+1)) (by positivity)
    _ = r^(k+1)*‖z-w‖ := by
      have hk : ((k+2 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

end Yau.LeafProofs.L17BanachLogarithmAux
