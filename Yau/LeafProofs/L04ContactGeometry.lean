import Mathlib

/-! Finite-difference geometry of affine supports for a semiconcave function. -/

open Set
open scoped InnerProductSpace

namespace Yau.LeafProofs.L04Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def AffineMinOn (φ : E → ℝ) (D : Set E) (x p : E) : Prop :=
  ∀ z ∈ D, φ x - ⟪p, x⟫_ℝ ≤ φ z - ⟪p, z⟫_ℝ

theorem affineMin_upper_of_symmetric_endpoints
    {φ : E → ℝ} {D U : Set E} {lam C : ℝ}
    (hsemi : ConvexOn ℝ U (fun z => -φ z + lam / 2 * ‖z‖ ^ 2))
    (hDU : D ⊆ U) (hC : lam ≤ C)
    {x p h : E} (hmin : AffineMinOn φ D x p)
    (hplus : x + h ∈ D) (hminus : x - h ∈ D) :
    φ (x + h) ≤ φ x + ⟪p, h⟫_ℝ + C * ‖h‖ ^ 2 := by
  have hmid := hsemi.2 (hDU hplus) (hDU hminus)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • (x + h) + (1 / 2 : ℝ) • (x - h) = x := by module
  rw [heq, smul_eq_mul, smul_eq_mul] at hmid
  dsimp only at hmid
  rw [norm_add_sq_real, norm_sub_sq_real] at hmid
  have hsupp := hmin (x - h) hminus
  rw [inner_sub_right] at hsupp
  have hbound := mul_le_mul_of_nonneg_right hC (sq_nonneg ‖h‖)
  nlinarith

theorem affineMin_slope_unique
    {φ : E → ℝ} {D U : Set E} {lam C ρ : ℝ}
    (hsemi : ConvexOn ℝ U (fun z => -φ z + lam / 2 * ‖z‖ ^ 2))
    (hDU : D ⊆ U) (hlam : lam ≤ C) (hC : 0 < C) (hρ : 0 < ρ)
    {x p q : E} (hxbuf : Metric.closedBall x ρ ⊆ D)
    (hp : AffineMinOn φ D x p) (hq : AffineMinOn φ D x q) :
    p = q := by
  by_contra hpq
  have ha : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  let t : ℝ := min (ρ / (‖p - q‖ + 1)) (1 / (2 * C))
  have ht : 0 < t := lt_min (div_pos hρ (by positivity)) (div_pos (by norm_num) (by positivity))
  have htρ : t * (‖p - q‖ + 1) ≤ ρ :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have htC : t * (2 * C) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let h : E := t • (p - q)
  have hnorm : ‖h‖ = t * ‖p - q‖ := by
    simp only [h, norm_smul, Real.norm_of_nonneg ht.le]
  have hh : ‖h‖ ≤ ρ := by rw [hnorm]; nlinarith
  have hplus : x + h ∈ D := hxbuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hh)
  have hminus : x - h ∈ D := hxbuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hh)
  have hu := affineMin_upper_of_symmetric_endpoints hsemi hDU hlam hq hplus hminus
  have hl := hp (x + h) hplus
  rw [inner_add_right] at hl
  have hinner : ⟪p - q, h⟫_ℝ = t * ‖p - q‖ ^ 2 := by
    dsimp only [h]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  rw [inner_sub_left] at hinner
  have hi : t * ‖p - q‖ ^ 2 ≤ C * (t * ‖p - q‖) ^ 2 := by
    rw [hnorm] at hu
    nlinarith
  have hi' : ‖p - q‖ ^ 2 ≤ (C * t) * ‖p - q‖ ^ 2 := by
    apply (mul_le_mul_iff_of_pos_left ht).mp
    convert hi using 1
    ring
  have hlt : (C * t) * ‖p - q‖ ^ 2 < ‖p - q‖ ^ 2 := by
    have : C * t < 1 := by nlinarith
    simpa only [one_mul] using mul_lt_mul_of_pos_right this (sq_pos_of_pos ha)
  exact (not_lt_of_ge hi') hlt

theorem affineMin_slope_local_bound
    {φ : E → ℝ} {D U : Set E} {lam C ρ : ℝ}
    (hsemi : ConvexOn ℝ U (fun z => -φ z + lam / 2 * ‖z‖ ^ 2))
    (hDU : D ⊆ U) (hlam : lam ≤ C) (hC : 0 < C) (hρ : 0 < ρ)
    {x y p q : E}
    (hxbuf : Metric.closedBall x ρ ⊆ D)
    (hybuf : Metric.closedBall y ρ ⊆ D)
    (hpx : AffineMinOn φ D x p) (hqy : AffineMinOn φ D y q)
    (hxy : ‖y - x‖ ≤ ρ) :
    ‖p - q‖ ≤ 2 * C * ‖y - x‖ := by
  by_cases hyx : y = x
  · subst y
    have hpq := affineMin_slope_unique hsemi hDU hlam hC hρ hxbuf hpx hqy
    simp [hpq]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  by_cases hpq : p = q
  · simp only [hpq, sub_self, norm_zero]
    positivity
  have ha : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  let h : E := (‖y - x‖ / ‖p - q‖) • (p - q)
  have hnorm : ‖h‖ = ‖y - x‖ := by
    simp only [h, norm_smul, Real.norm_of_nonneg (div_nonneg hd.le ha.le)]
    exact div_mul_cancel₀ _ ha.ne'
  have hyplus : y + h ∈ D := hybuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm] using hxy)
  have hyminus : y - h ∈ D := hybuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      hnorm] using hxy)
  have hxplus : x + (y - x) ∈ D := hxbuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hxy)
  have hxmin : x - (y - x) ∈ D := hxbuf (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hxy)
  have hu0 := affineMin_upper_of_symmetric_endpoints hsemi hDU hlam hpx hxplus hxmin
  have hu1 := affineMin_upper_of_symmetric_endpoints hsemi hDU hlam hqy hyplus hyminus
  have hlow := hpx (y + h) hyplus
  have hxadd : x + (y - x) = y := by abel
  rw [hxadd, inner_sub_right] at hu0
  rw [hnorm] at hu1
  rw [inner_add_right] at hlow
  have hinner : ⟪p - q, h⟫_ℝ = ‖y - x‖ * ‖p - q‖ := by
    dsimp only [h]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [inner_sub_left] at hinner
  have hi : ‖y - x‖ * ‖p - q‖ ≤ ‖y - x‖ * (2 * C * ‖y - x‖) := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hd).mp hi

end Yau.LeafProofs.L04Aux
