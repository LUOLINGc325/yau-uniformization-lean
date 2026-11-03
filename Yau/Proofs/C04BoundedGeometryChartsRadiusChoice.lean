import Mathlib

/-! A normal radius depending only on the prescribed scalar data. -/

noncomputable section
namespace Yau.Proofs.C04ChartsAux

theorem exists_uniform_normal_radius {r K D : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hD : 0 ≤ D) :
    ∃ s : ℝ, 0 < s ∧ Real.sqrt 2 * (4 * s) < 2 * r ∧
      D * K * (2 * (4 * s) ^ 2) ≤ (1 / 8 : ℝ) := by
  have hrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let a := D * K
  have ha : 0 ≤ a := mul_nonneg hD hK.le
  let s := min (r / (8 * Real.sqrt 2)) (1 / (16 * (1 + a)))
  have hs : 0 < s := lt_min (div_pos hr (by positivity)) (by positivity)
  have hs₁ : s ≤ r / (8 * Real.sqrt 2) := min_le_left _ _
  have hs₂ : s ≤ 1 / (16 * (1 + a)) := min_le_right _ _
  have hs₂' : 16 * (1 + a) * s ≤ 1 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (1 + a))).mp hs₂
    nlinarith
  have hsa : 0 ≤ a * s := mul_nonneg ha hs.le
  have hs16 : s ≤ 1 / 16 := by nlinarith
  have has16 : a * s ≤ 1 / 16 := by nlinarith
  have hprod : a * s * s ≤ 1 / 256 := by
    have H := mul_le_mul has16 hs16 hs.le (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith
  refine ⟨s, hs, ?_, ?_⟩
  · have H := (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 2)).mp hs₁
    nlinarith
  · change a * (2 * (4 * s) ^ 2) ≤ _
    nlinarith

end Yau.Proofs.C04ChartsAux
