import Yau.LeafProofs.L19HeatFamilyMultiplier

/-! Uniform weighted initial-generator estimates for the fixed scalar heat multiplier. -/

noncomputable section
open scoped Topology

namespace Yau.Proofs.F03Aux
open Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exp_neg_remainder_bounds (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ Real.exp (-x) - 1 + x ∧ Real.exp (-x) - 1 + x ≤ x ^ 2 := by
  have hlo : 0 ≤ Real.exp (-x) - 1 + x := by
    nlinarith only [Real.add_one_le_exp (-x)]
  refine ⟨hlo, ?_⟩
  by_cases hsmall : x ≤ 1
  · have hn : ‖(-x)‖ ≤ 1 := by simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg hx]
      using hsmall
    have hb := Real.norm_exp_sub_one_sub_id_le hn
    simpa only [sub_neg_eq_add, Real.norm_eq_abs, abs_of_nonneg hlo,
      abs_neg, abs_of_nonneg hx] using hb
  · have hlarge : 1 ≤ x := (lt_of_not_ge hsmall).le
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
    nlinarith only [he, hlarge]

def heatDifferenceMultiplier (t r : ℝ) : ℝ := (scalarHeatMultiplier t r - 1) * r / t

theorem heatDifferenceMultiplier_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (heatDifferenceMultiplier t) :=
  (((scalarHeatMultiplier_continuous ht).sub continuous_const).mul continuous_id).div_const t

theorem heatDifferenceMultiplier_bound {t r : ℝ} (ht : 0 < t) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖heatDifferenceMultiplier t r‖ ≤ 1 := by
  rw [heatDifferenceMultiplier, norm_div, Real.norm_of_nonneg ht.le, div_le_one ht]
  exact scalarHeatMultiplier_initial_bound ht.le hr

theorem heatDifferenceMultiplier_weighted_error {t r : ℝ}
    (ht : 0 < t) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖(heatDifferenceMultiplier t r - (r - 1)) * r‖ ≤ t := by
  by_cases hr₀ : r = 0
  · simp only [hr₀, mul_zero, norm_zero]
    exact ht.le
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr₀)
  let x := t * ((1 - r) / r)
  have hx : 0 ≤ x := mul_nonneg ht.le (div_nonneg (sub_nonneg.mpr hr.2) hr.1)
  have hb := exp_neg_remainder_bounds x hx
  have hq : 0 ≤ r ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have he : -t * (r⁻¹ - 1) = -x := by
    dsimp [x]
    field_simp <;> ring
  have hid : (heatDifferenceMultiplier t r - (r - 1)) * r =
      (Real.exp (-x) - 1 + x) * (r ^ 2 / t) := by
    rw [heatDifferenceMultiplier, scalarHeatMultiplier_of_pos t hrpos, he]
    dsimp [x]
    field_simp <;> ring
  have hsq : (1 - r) ^ 2 ≤ 1 := by nlinarith only [hr.1, hr.2]
  rw [hid, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 hq)]
  calc
    _ ≤ x ^ 2 * (r ^ 2 / t) := mul_le_mul_of_nonneg_right hb.2 hq
    _ = t * (1 - r) ^ 2 := by
      dsimp [x]
      field_simp <;> ring
    _ ≤ t := by nlinarith only [mul_le_mul_of_nonneg_left hsq ht.le]

end Yau.Proofs.F03Aux
