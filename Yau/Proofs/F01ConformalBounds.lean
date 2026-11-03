import Yau.Proofs.F01ConformalProfile

/-! Uncompiled F01 scratch: bounds of the actual explicit profile derivatives.
The single numerical bound is chosen before the sublevel parameter L. -/
open Set Filter
open scoped Topology
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem conformalProfile_exp_half {v : ℝ} (hv : 3 / 4 ≤ v) (h1 : v < 1) :
    Real.exp (-conformalProfile v / 2) = 1 - v := by
  rw [conformalProfile_log hv]
  have he : -(-2 * Real.log (1 - v)) / 2 = Real.log (1 - v) := by ring
  rw [he, Real.exp_log (sub_pos.mpr h1)]

theorem conformalProfile_exp_neg {v : ℝ} (hv : 3 / 4 ≤ v) (h1 : v < 1) :
    Real.exp (-conformalProfile v) = (1 - v) ^ 2 := by
  rw [conformalProfile_log hv]
  have he : -(-2 * Real.log (1 - v)) =
      Real.log (1 - v) + Real.log (1 - v) := by ring
  rw [he, Real.exp_add, Real.exp_log (sub_pos.mpr h1)]
  ring

theorem conformalProfile_deriv_of_large {v : ℝ} (hv : 3 / 4 < v) (h1 : v < 1) :
    deriv conformalProfile v = 2 / (1 - v) := by
  have hnear : conformalProfile =ᶠ[𝓝 v] (fun w => -2 * Real.log (1 - w)) := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    exact conformalProfile_log hw.le
  have hsub : HasDerivAt (fun w : ℝ => 1 - w) (-1) v := by
    simpa only [id_eq] using (hasDerivAt_id v).const_sub 1
  have hl : HasDerivAt (fun w : ℝ => Real.log (1 - w)) (-1 / (1 - v)) v :=
    hsub.log (sub_pos.mpr h1).ne' 
  have hd : HasDerivAt (fun w : ℝ => -2 * Real.log (1 - w)) (2 / (1 - v)) v := by
    convert hl.const_mul (-2) using 1 <;> ring
  exact hnear.deriv_eq.trans hd.deriv

theorem conformalProfile_deriv_two_of_large {v : ℝ} (hv : 3 / 4 < v) (h1 : v < 1) :
    deriv (deriv conformalProfile) v = 2 / (1 - v) ^ 2 := by
  have hnear : deriv conformalProfile =ᶠ[𝓝 v] (fun w => 2 / (1 - w)) := by
    filter_upwards [Ioi_mem_nhds hv, Iio_mem_nhds h1] with w hw0 hw1
    exact conformalProfile_deriv_of_large hw0 hw1
  have hsub : HasDerivAt (fun w : ℝ => 1 - w) (-1) v := by
    simpa only [id_eq] using (hasDerivAt_id v).const_sub 1
  have hd : HasDerivAt (fun w : ℝ => 2 / (1 - w)) (2 / (1 - v) ^ 2) v := by
    simpa only [div_eq_mul_inv, neg_neg, one_mul, Pi.inv_apply] using
      (hsub.inv (sub_pos.mpr h1).ne').const_mul (2 : ℝ)
  exact hnear.deriv_eq.trans hd.deriv

theorem conformalProfile_weighted_first_of_large {v : ℝ}
    (hv : 3 / 4 < v) (h1 : v < 1) :
    Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v| = 2 := by
  rw [conformalProfile_exp_half hv.le h1, conformalProfile_deriv_of_large hv h1,
    abs_of_nonneg (div_nonneg (by norm_num) (sub_pos.mpr h1).le)]
  field_simp [(sub_pos.mpr h1).ne']

theorem conformalProfile_weighted_second_of_large {v : ℝ}
    (hv : 3 / 4 < v) (h1 : v < 1) :
    Real.exp (-conformalProfile v) *
      (|deriv (deriv conformalProfile) v| + |deriv conformalProfile v|) =
      2 + 2 * (1 - v) := by
  rw [conformalProfile_exp_neg hv.le h1, conformalProfile_deriv_two_of_large hv h1,
    conformalProfile_deriv_of_large hv h1,
    abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _)),
    abs_of_nonneg (div_nonneg (by norm_num) (sub_pos.mpr h1).le)]
  field_simp [(sub_pos.mpr h1).ne']

/-- The fixed profile constant simultaneously controls the terms needed for
|∂F(u/L)|_{exp(F)g} and levi(F(u/L)) measured in the actual conformal metric. -/
theorem conformalProfile_weighted_derivative_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ v ∈ Ico (0 : ℝ) 1,
      Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v| ≤ C ∧
      Real.exp (-conformalProfile v) *
        (|deriv (deriv conformalProfile) v| + |deriv conformalProfile v|) ≤ C := by
  have hD : ContDiffOn ℝ ∞ (deriv conformalProfile) (Iio 1) :=
    conformalProfile_contDiffOn.deriv_of_isOpen isOpen_Iio (by simp)
  have hDD : ContDiffOn ℝ ∞ (deriv (deriv conformalProfile)) (Iio 1) :=
    hD.deriv_of_isOpen isOpen_Iio (by simp)
  have hsub : Icc (0 : ℝ) (7 / 8) ⊆ Iio 1 := by
    intro v hv
    exact lt_of_le_of_lt hv.2 (by norm_num)
  have hA : ContinuousOn (fun v : ℝ =>
      Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v|) (Icc 0 (7 / 8)) :=
    (((conformalProfile_contDiffOn.continuousOn.neg.div_const 2).rexp).mul
      hD.continuousOn.abs).mono hsub
  have hB : ContinuousOn (fun v : ℝ => Real.exp (-conformalProfile v) *
      (|deriv (deriv conformalProfile) v| + |deriv conformalProfile v|))
      (Icc 0 (7 / 8)) :=
    ((conformalProfile_contDiffOn.continuousOn.neg.rexp).mul
      (hDD.continuousOn.abs.add hD.continuousOn.abs)).mono hsub
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hB
  refine ⟨max 6 (max A B) + 1, by positivity, ?_⟩
  intro v hv
  by_cases hs : v ≤ 7 / 8
  · have hAc := hA v ⟨hv.1, hs⟩
    have hBc := hB v ⟨hv.1, hs⟩
    have ha : A ≤ max 6 (max A B) := (le_max_left _ _).trans (le_max_right _ _)
    have hb : B ≤ max 6 (max A B) := (le_max_right _ _).trans (le_max_right _ _)
    constructor
    · have ht : Real.exp (-conformalProfile v / 2) * |deriv conformalProfile v| ≤ A :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hAc)
      linarith
    · have ht : Real.exp (-conformalProfile v) *
          (|deriv (deriv conformalProfile) v| + |deriv conformalProfile v|) ≤ B :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBc)
      linarith
  · have hl : 3 / 4 < v := by linarith
    rw [conformalProfile_weighted_first_of_large hl hv.2,
      conformalProfile_weighted_second_of_large hl hv.2]
    have hc : 6 ≤ max 6 (max A B) := le_max_left _ _
    constructor <;> linarith

end Yau.NodeProofs.F01Aux
