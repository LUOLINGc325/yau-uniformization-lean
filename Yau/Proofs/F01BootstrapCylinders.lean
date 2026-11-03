import Yau.Proofs.F01BufferedParabolicPatches

/-! A nested family of actual cylinders for the spatial induction.
Every order contains the same half-radius, half-time core; the affine
patch scale is determined by the order before any solution is chosen. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def bootstrapRadius (k : ℕ) : ℝ := 1 / 2 + (1 / 2 : ℝ) ^ (k + 1)
def bootstrapScale (k : ℕ) : ℝ := (bootstrapRadius k - bootstrapRadius (k + 1)) / 4
def bootstrapCylinder (n k : ℕ) : Set (Point n) :=
  cylinder (ball 0 (bootstrapRadius k)) (-bootstrapRadius k) (1 / 2)

theorem bootstrapRadius_zero : bootstrapRadius 0 = 1 := by norm_num [bootstrapRadius]

theorem bootstrapRadius_bounds (k : ℕ) : 1 / 2 < bootstrapRadius k ∧ bootstrapRadius k ≤ 1 := by
  have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  have hle : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have hk : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  constructor <;> dsimp only [bootstrapRadius] <;> linarith

theorem bootstrapScale_eq (k : ℕ) : bootstrapScale k = (1 / 2 : ℝ) ^ (k + 1) / 8 := by
  simp only [bootstrapScale, bootstrapRadius, pow_succ]
  ring

theorem bootstrap_buffer_data (k : ℕ) :
    0 < bootstrapScale k ∧ bootstrapScale k ≤ 1 ∧
      bootstrapRadius (k + 1) + 2 * bootstrapScale k ≤ bootstrapRadius k ∧
      -bootstrapRadius k + 4 * (bootstrapScale k) ^ 2 ≤ -bootstrapRadius (k + 1) ∧
      -bootstrapRadius (k + 1) < (1 / 2 : ℝ) := by
  have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  have hp1 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnext : bootstrapRadius (k + 1) = 1 / 2 + (1 / 2 : ℝ) ^ (k + 1) / 2 := by
    simp only [bootstrapRadius, pow_succ]
    ring
  rw [bootstrapScale_eq, hnext]
  change 0 < (1 / 2 : ℝ) ^ (k + 1) / 8 ∧ _
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · dsimp only [bootstrapRadius]
    linarith
  constructor
  · dsimp only [bootstrapRadius]
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  · linarith

theorem bootstrapCylinder_mono_step (k : ℕ) : bootstrapCylinder n (k + 1) ⊆ bootstrapCylinder n k := by
  have hb := bootstrap_buffer_data k
  have hrad : bootstrapRadius (k + 1) ≤ bootstrapRadius k := by linarith [hb.1]
  intro p hp
  exact ⟨Metric.ball_subset_ball hrad hp.1, by linarith [hp.2.1], hp.2.2⟩

theorem bootstrap_core_subset (k : ℕ) :
    cylinder (ball (0 : Space n) (1 / 2)) (-(1 / 2)) (1 / 2) ⊆ bootstrapCylinder n k := by
  have hr := (bootstrapRadius_bounds k).1.le
  intro p hp
  exact ⟨Metric.ball_subset_ball hr hp.1, by linarith [hp.2.1], hp.2.2⟩

end Yau.NodeProofs.F01Aux
