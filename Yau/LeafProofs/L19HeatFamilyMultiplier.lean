import Yau.LeafProofs.L19HeatFamilyComplexification
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! The continuous bounded spectral multiplier, including its spectral-zero endpoint. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Positive-time heat multiplier in the bounded resolvent parameter. -/
def scalarHeatMultiplier (t s : ℝ) : ℝ :=
  if 0 < s then Real.exp (-t * (s⁻¹ - 1)) else 0

@[simp] theorem scalarHeatMultiplier_zero (t : ℝ) : scalarHeatMultiplier t 0 = 0 := by
  simp [scalarHeatMultiplier]

theorem scalarHeatMultiplier_of_pos (t : ℝ) {s : ℝ} (hs : 0 < s) :
    scalarHeatMultiplier t s = Real.exp (-t * (s⁻¹ - 1)) := by
  simp [scalarHeatMultiplier, hs]

/-- The glued exponential supplies actual continuity at spectral zero. -/
theorem scalarHeatMultiplier_eq_glue {t : ℝ} (ht : 0 < t) (s : ℝ) :
    scalarHeatMultiplier t s = Real.exp t * expNegInvGlue (s / t) := by
  by_cases hs : 0 < s
  · rw [scalarHeatMultiplier_of_pos t hs, expNegInvGlue,
      ite_eq_right (not_le.mpr (div_pos hs ht)), ← Real.exp_add]
    congr 1
    field_simp
    ring
  · rw [scalarHeatMultiplier, ite_eq_right hs,
      expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hs) ht.le),
      mul_zero]

theorem scalarHeatMultiplier_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (scalarHeatMultiplier t) := by
  change Continuous (fun s => scalarHeatMultiplier t s)
  simp_rw [scalarHeatMultiplier_eq_glue ht]
  exact continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp
    (continuous_id.div_const t))

theorem scalarHeatMultiplier_nonneg (t s : ℝ) : 0 ≤ scalarHeatMultiplier t s := by
  unfold scalarHeatMultiplier
  split_ifs <;> positivity

theorem scalarHeatMultiplier_le_one {t s : ℝ} (ht : 0 ≤ t) (hs : s ≤ 1) :
    scalarHeatMultiplier t s ≤ 1 := by
  by_cases hs₀ : 0 < s
  · rw [scalarHeatMultiplier_of_pos t hs₀]
    apply Real.exp_le_one_iff.mpr
    have hinv : 1 ≤ s⁻¹ := (one_le_inv₀ hs₀).mpr hs
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sub_nonneg.mpr hinv)
  · simp [scalarHeatMultiplier, hs₀]

theorem scalarHeatMultiplier_add (s t x : ℝ) :
    scalarHeatMultiplier (s + t) x = scalarHeatMultiplier s x * scalarHeatMultiplier t x := by
  by_cases hx : 0 < x
  · simp only [scalarHeatMultiplier_of_pos _ hx, ← Real.exp_add]
    congr 1
    ring
  · simp [scalarHeatMultiplier, hx]

/-- The factor of the resolvent removes the nonuniformity at spectral zero. -/
theorem scalarHeatMultiplier_initial_bound {t s : ℝ} (ht : 0 ≤ t)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖(scalarHeatMultiplier t s - 1) * s‖ ≤ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1,
    abs_of_nonpos (sub_nonpos.mpr (scalarHeatMultiplier_le_one ht hs.2))]
  by_cases hs₀ : 0 < s
  · have hinv : 0 ≤ s⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hs₀).mpr hs.2)
    have hExp := Real.add_one_le_exp (-t * (s⁻¹ - 1))
    rw [← scalarHeatMultiplier_of_pos t hs₀] at hExp
    have hmul := mul_le_mul_of_nonneg_right hExp hs.1
    have hsne : s ≠ 0 := ne_of_gt hs₀
    have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ hsne
    nlinarith [mul_nonneg ht hs.1]
  · have hz : s = 0 := le_antisymm (le_of_not_gt hs₀) hs.1
    simp [hz, ht]

end Yau.LeafProofs.L19Aux
