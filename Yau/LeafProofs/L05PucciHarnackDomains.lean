import Yau.LeafProofs.L05PucciHarnackAffine

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_affine_space_dist {n : ℕ} (c : Space n) {R : ℝ} (a T : ℝ)
    (hR : 0 < R) (z : Point n) : dist (harnackAffine c R a T z).1 c=R*‖z.1‖ := by
  rw [harnack_affine_apply]
  change dist (c+R • z.1) c=R*‖z.1‖
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR]

theorem harnack_affine_closed_mem_iff {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (z : Point n) :
    harnackAffine c R a T z ∈ harnackClosed c R a T ↔ z ∈ unitClosed n := by
  have hDist := harnack_affine_space_dist c a T hR z
  change (dist (harnackAffine c R a T z).1 c ≤ R ∧
      a ≤ (harnackAffine c R a T z).2 ∧ (harnackAffine c R a T z).2 ≤ a+T) ↔
    (dist z.1 0 ≤ 1 ∧ (-1 : ℝ) ≤ z.2 ∧ z.2 ≤ 0)
  rw [hDist,harnack_affine_apply]
  simp only [dist_zero_right]
  constructor
  · intro hz
    have hx : ‖z.1‖ ≤ 1 := (mul_le_mul_iff_of_pos_left hR).mp (by simpa only [mul_one] using hz.1)
    have hl : 0 ≤ T*(z.2+1) := by linarith [hz.2.1]
    have hu : T*(z.2+1) ≤ T := by linarith [hz.2.2]
    have hl' : (0 : ℝ) ≤ z.2+1 := (mul_le_mul_iff_of_pos_left hT).mp (by simpa only [mul_zero] using hl)
    have hu' : z.2+1 ≤ 1 := (mul_le_mul_iff_of_pos_left hT).mp (by simpa only [mul_one] using hu)
    exact ⟨hx,by linarith,by linarith⟩
  · intro hz
    have hx := (mul_le_mul_iff_of_pos_left hR).mpr hz.1
    have hl := mul_le_mul_of_nonneg_left (by linarith [hz.2.1] : (0 : ℝ) ≤ z.2+1) hT.le
    have hu := mul_le_mul_of_nonneg_left (by linarith [hz.2.2] : z.2+1 ≤ 1) hT.le
    exact ⟨by simpa only [mul_one] using hx,by nlinarith only [hl],by nlinarith only [hu]⟩

theorem harnack_affine_open_mem_iff {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) (z : Point n) :
    harnackAffine c R a T z ∈ harnackOpen c R a T ↔ z ∈ unitOpen n := by
  have hDist := harnack_affine_space_dist c a T hR z
  change (dist (harnackAffine c R a T z).1 c < R ∧
      a < (harnackAffine c R a T z).2 ∧ (harnackAffine c R a T z).2 < a+T) ↔
    (dist z.1 0 < 1 ∧ (-1 : ℝ) < z.2 ∧ z.2 < 0)
  rw [hDist,harnack_affine_apply]
  simp only [dist_zero_right]
  constructor
  · intro hz
    have hx : ‖z.1‖ < 1 := (mul_lt_mul_iff_of_pos_left hR).mp (by simpa only [mul_one] using hz.1)
    have hl : 0 < T*(z.2+1) := by linarith [hz.2.1]
    have hu : T*(z.2+1) < T := by linarith [hz.2.2]
    have hl' : (0 : ℝ) < z.2+1 := (mul_lt_mul_iff_of_pos_left hT).mp (by simpa only [mul_zero] using hl)
    have hu' : z.2+1 < 1 := (mul_lt_mul_iff_of_pos_left hT).mp (by simpa only [mul_one] using hu)
    exact ⟨hx,by linarith,by linarith⟩
  · intro hz
    have hx := (mul_lt_mul_iff_of_pos_left hR).mpr hz.1
    have hl := mul_lt_mul_of_pos_left (by linarith [hz.2.1] : (0 : ℝ) < z.2+1) hT
    have hu := mul_lt_mul_of_pos_left (by linarith [hz.2.2] : z.2+1 < 1) hT
    exact ⟨by simpa only [mul_one] using hx,by nlinarith only [hl],by nlinarith only [hu]⟩

theorem harnack_affine_maps_boundary {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) {z : Point n} (hz : z ∈ parabolicBoundary n) :
    harnackAffine c R a T z ∈ harnackBoundary c R a T := by
  have hClosed := (harnack_affine_closed_mem_iff (a := a) c hR hT z).mpr (harnack_boundary_subset_unitClosed hz)
  rcases hz with hz | hz
  · refine Or.inl ⟨hClosed.1,?_⟩
    have ht : z.2=(-1 : ℝ) := hz.2
    change (harnackAffine c R a T z).2=a
    rw [harnack_affine_apply]
    simp only [ht,neg_add_cancel,mul_zero,add_zero]
  · refine Or.inr ⟨?_,hClosed.2⟩
    have hx : ‖z.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1
    change dist (harnackAffine c R a T z).1 c=R
    rw [harnack_affine_space_dist c a T hR z,hx,mul_one]

theorem harnack_affine_image_closed {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) :
    harnackAffine c R a T '' unitClosed n=harnackClosed c R a T := by
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (harnack_affine_closed_mem_iff (a := a) c hR hT z).mpr hz
  · intro hp
    refine ⟨harnackAffineInv c R a T p,?_,harnack_affine_apply_inv hR.ne' hT.ne' p⟩
    exact (harnack_affine_closed_mem_iff (a := a) c hR hT _).mp
      (by rwa [harnack_affine_apply_inv hR.ne' hT.ne'])

theorem harnack_affine_image_open {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : 0 < R) (hT : 0 < T) :
    harnackAffine c R a T '' unitOpen n=harnackOpen c R a T := by
  ext p
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (harnack_affine_open_mem_iff (a := a) c hR hT z).mpr hz
  · intro hp
    refine ⟨harnackAffineInv c R a T p,?_,harnack_affine_apply_inv hR.ne' hT.ne' p⟩
    exact (harnack_affine_open_mem_iff (a := a) c hR hT _).mp
      (by rwa [harnack_affine_apply_inv hR.ne' hT.ne'])

def harnackAffineHomeomorph {n : ℕ} (c : Space n) {R a T : ℝ}
    (hR : R≠0) (hT : T≠0) : Point n ≃ₜ Point n where
  toFun := harnackAffine c R a T
  invFun := harnackAffineInv c R a T
  left_inv := harnack_affine_inv_apply hR hT
  right_inv := harnack_affine_apply_inv hR hT
  continuous_toFun := (harnack_affine_contDiff c R a T).continuous
  continuous_invFun := (harnack_affineInv_contDiff c R a T).continuous

end Yau.LeafProofs.L05Aux
