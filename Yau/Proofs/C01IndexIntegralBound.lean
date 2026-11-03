import Yau.Proofs.C01IndexCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A weighted index estimate controls the full nonnegative Ricci
integral; only the two short endpoint strips use the pointwise bound. -/

noncomputable section
open MeasureTheory
open scoped Topology Interval

namespace Yau.NodeProofs.C01Aux

theorem index_integral_bound_of_weighted
    (R : ℝ → ℝ) (hR : ContinuousOn R (Set.Icc (0 : ℝ) 1))
    (hRnonneg : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R u)
    (κ C A : ℝ) (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1, R u ≤ C)
    (hindex : (∫ u in (0 : ℝ)..1, indexCutoff κ u ^ 2 * R u) ≤ A) :
    (∫ u in (0 : ℝ)..1, R u) ≤ A + 2 * κ * C := by
  let Q : ℝ → ℝ := fun u => (1 - indexCutoff κ u ^ 2) * R u
  have hφ := (indexCutoff_contDiff κ).continuous
  have hQ : ContinuousOn Q (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub (hφ.pow 2)).continuousOn.mul hR
  have hP : ContinuousOn (fun u => indexCutoff κ u ^ 2 * R u) (Set.Icc (0 : ℝ) 1) :=
    (hφ.pow 2).continuousOn.mul hR
  have hκ1 : κ ≤ 1 := by linarith
  have hmiddle : κ ≤ 1 - κ := by linarith
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
      IntervalIntegrable Q volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hQ.mono (Set.Icc_subset_Icc ha hb)
  have hPi : IntervalIntegrable (fun u => indexCutoff κ u ^ 2 * R u) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le zero_le_one] using hP
  have hQi := hi 0 1 le_rfl zero_le_one le_rfl
  have hQle (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : Q u ≤ C := by
    have hp := mul_nonneg (sq_nonneg (indexCutoff κ u)) (hRnonneg u hu)
    dsimp only [Q]
    nlinarith [hbound u hu]
  have hleft : (∫ u in (0 : ℝ)..κ, Q u) ≤ κ * C := by
    have H := intervalIntegral.integral_mono_on hκ.le (hi 0 κ le_rfl hκ.le hκ1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 κ)
      (fun u hu => hQle u ⟨hu.1, hu.2.trans hκ1⟩)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using H
  have hright : (∫ u in (1 - κ)..(1 : ℝ), Q u) ≤ κ * C := by
    have H := intervalIntegral.integral_mono_on (by linarith : 1 - κ ≤ 1)
      (hi (1 - κ) 1 (by linarith) (by linarith) le_rfl)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (1 - κ) 1)
      (fun u hu => hQle u ⟨(by linarith [hu.1]), hu.2⟩)
    convert H using 1 <;> simp only [intervalIntegral.integral_const, smul_eq_mul] <;> ring
  have hmid : (∫ u in κ..(1 - κ), Q u) = 0 := by
    have heq : Set.EqOn Q (fun _ => (0 : ℝ)) (Set.uIcc κ (1 - κ)) := by
      intro u hu
      have hu' : u ∈ Set.Icc κ (1 - κ) := by simpa only [Set.uIcc_of_le hmiddle] using hu
      simp only [Q, indexCutoff_one_middle hκ hu'.1 hu'.2, one_pow, sub_self, zero_mul]
    rw [intervalIntegral.integral_congr heq]
    simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 κ le_rfl hκ.le hκ1) (hi κ (1 - κ) hκ.le hmiddle (by linarith))
  have hsplit' := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (1 - κ) le_rfl (by linarith) (by linarith))
    (hi (1 - κ) 1 (by linarith) (by linarith) le_rfl)
  have hQbound : (∫ u in (0 : ℝ)..1, Q u) ≤ 2 * κ * C := by
    rw [hmid, add_zero] at hsplit
    rw [← hsplit', ← hsplit]
    nlinarith [hleft, hright]
  have hid : (fun u => indexCutoff κ u ^ 2 * R u + Q u) = R := by
    funext u
    dsimp only [Q]
    ring
  have hsum := intervalIntegral.integral_add hPi hQi
  rw [hid] at hsum
  linarith

end Yau.NodeProofs.C01Aux
