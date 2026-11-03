import Yau.LeafProofs.L05PucciHarnackCube

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_parabolic_affine_apply {n : ℕ} (c : Space n) (r a : ℝ) (z : Point n) :
    harnackAffine c r (a-r^2) (r^2) z=(c+r • z.1,a+r^2*z.2) := by
  rw [harnack_affine_apply]
  congr 1
  ring

theorem harnack_parabolic_closed_mem_iff {n : ℕ} (c : Space n) {r a : ℝ}
    (hr : 0 < r) (R s T : ℝ) (z : Point n) :
    harnackAffine c r (a-r^2) (r^2) z∈harnackClosed c (r*R) (a+r^2*s) (r^2*T) ↔
      z∈harnackClosed 0 R s T := by
  have hDist := harnack_affine_space_dist c (a-r^2) (r^2) hr z
  change (dist (harnackAffine c r (a-r^2) (r^2) z).1 c ≤ r*R ∧
    a+r^2*s ≤ (harnackAffine c r (a-r^2) (r^2) z).2 ∧
    (harnackAffine c r (a-r^2) (r^2) z).2 ≤ a+r^2*s+r^2*T) ↔
      (dist z.1 0 ≤ R ∧ s ≤ z.2 ∧ z.2 ≤ s+T)
  rw [hDist,harnack_parabolic_affine_apply,dist_zero_right]
  have hr2 := sq_pos_of_ne_zero hr.ne'
  constructor
  · rintro ⟨hx,hl,hu⟩
    have hl' : r^2*s ≤ r^2*z.2 := by linarith
    have hu' : r^2*z.2 ≤ r^2*(s+T) := by nlinarith only [hu]
    exact ⟨(mul_le_mul_iff_of_pos_left hr).mp hx,
      (mul_le_mul_iff_of_pos_left hr2).mp hl',(mul_le_mul_iff_of_pos_left hr2).mp hu'⟩
  · rintro ⟨hx,hl,hu⟩
    have hl' := mul_le_mul_of_nonneg_left hl hr2.le
    have hu' := mul_le_mul_of_nonneg_left hu hr2.le
    exact ⟨mul_le_mul_of_nonneg_left hx hr.le,by linarith,by nlinarith only [hu']⟩

theorem harnack_parabolic_open_mem_iff {n : ℕ} (c : Space n) {r a : ℝ}
    (hr : 0 < r) (R s T : ℝ) (z : Point n) :
    harnackAffine c r (a-r^2) (r^2) z∈harnackOpen c (r*R) (a+r^2*s) (r^2*T) ↔
      z∈harnackOpen 0 R s T := by
  have hDist := harnack_affine_space_dist c (a-r^2) (r^2) hr z
  change (dist (harnackAffine c r (a-r^2) (r^2) z).1 c < r*R ∧
    a+r^2*s < (harnackAffine c r (a-r^2) (r^2) z).2 ∧
    (harnackAffine c r (a-r^2) (r^2) z).2 < a+r^2*s+r^2*T) ↔
      (dist z.1 0 < R ∧ s < z.2 ∧ z.2 < s+T)
  rw [hDist,harnack_parabolic_affine_apply,dist_zero_right]
  have hr2 := sq_pos_of_ne_zero hr.ne'
  constructor
  · rintro ⟨hx,hl,hu⟩
    have hl' : r^2*s < r^2*z.2 := by linarith
    have hu' : r^2*z.2 < r^2*(s+T) := by nlinarith only [hu]
    exact ⟨(mul_lt_mul_iff_of_pos_left hr).mp hx,
      (mul_lt_mul_iff_of_pos_left hr2).mp hl',(mul_lt_mul_iff_of_pos_left hr2).mp hu'⟩
  · rintro ⟨hx,hl,hu⟩
    have hl' := mul_lt_mul_of_pos_left hl hr2
    have hu' := mul_lt_mul_of_pos_left hu hr2
    exact ⟨mul_lt_mul_of_pos_left hx hr,by linarith,by nlinarith only [hu']⟩

end Yau.LeafProofs.L05Aux
