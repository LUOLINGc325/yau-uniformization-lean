import Mathlib

noncomputable section

namespace Yau.NodeProofs.P06Aux.Clip

def intervalClip (C r : ℝ) : ℝ := min C (max (-C) r)

theorem intervalClip_lipschitz (C : ℝ) : LipschitzWith 1 (intervalClip C) := by
  exact (LipschitzWith.id.const_max (-C)).const_min C

theorem intervalClip_monotone (C : ℝ) : Monotone (intervalClip C) :=
  monotone_const.min (monotone_const.max monotone_id)

theorem intervalClip_mem {C : ℝ} (hC : 0 ≤ C) (r : ℝ) : intervalClip C r ∈ Set.Icc (-C) C := by
  exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩

theorem intervalClip_zero {C : ℝ} (hC : 0 ≤ C) : intervalClip C 0 = 0 := by
  rw [intervalClip, max_eq_right (neg_nonpos.mpr hC), min_eq_right hC]

theorem intervalClip_eq_self {C r : ℝ} (hr : r ∈ Set.Icc (-C) C) : intervalClip C r = r := by
  rw [intervalClip, max_eq_right hr.1, min_eq_right hr.2]

theorem intervalClip_residual {C : ℝ} (hC : 0 ≤ C) (r : ℝ) :
    r - intervalClip C r = max (r - C) 0 - max (-r - C) 0 := by
  by_cases hu : C ≤ r
  · rw [intervalClip, min_eq_left (le_max_of_le_right hu),
      max_eq_left (sub_nonneg.mpr hu), max_eq_right (by linarith)]
    ring
  · by_cases hl : r ≤ -C
    · rw [intervalClip, max_eq_left hl, min_eq_right (by linarith),
        max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [intervalClip, max_eq_right (le_of_not_ge hl), min_eq_right (le_of_not_ge hu),
        max_eq_right (by linarith), max_eq_right (by linarith)]
      ring

theorem intervalClip_upper_orthogonal (C r : ℝ) : max (r - C) 0 * (C - intervalClip C r) = 0 := by
  by_cases hu : C ≤ r
  · rw [intervalClip, min_eq_left (le_max_of_le_right hu), sub_self, mul_zero]
  · rw [max_eq_right (by linarith : r - C ≤ 0), zero_mul]

theorem intervalClip_lower_orthogonal {C : ℝ} (hC : 0 ≤ C) (r : ℝ) :
    max (-r - C) 0 * (intervalClip C r + C) = 0 := by
  by_cases hl : r ≤ -C
  · rw [intervalClip, max_eq_left hl, min_eq_right (by linarith), neg_add_cancel, mul_zero]
  · rw [max_eq_right (by linarith : -r - C ≤ 0), zero_mul]

end Yau.NodeProofs.P06Aux.Clip
