import Yau.Proofs.C01IndexCutoff

/-! The fixed smooth cutoff has a dimension-free derivative bound.
Dividing it by the interval parameter remains smooth because it is
identically zero near the initial endpoint. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

theorem indexCutoff_hasDerivAt (κ u : ℝ) :
    HasDerivAt (indexCutoff κ)
      ((2 / κ) * deriv Real.smoothTransition (2 * u / κ - 1) *
        Real.smoothTransition (2 * (1 - u) / κ - 1) -
       (2 / κ) * Real.smoothTransition (2 * u / κ - 1) *
        deriv Real.smoothTransition (2 * (1 - u) / κ - 1)) u := by
  have hA : HasDerivAt (fun s : ℝ => 2 * s / κ - 1) (2 / κ) u := by
    convert ((hasDerivAt_id u).const_mul (2 / κ)).sub_const 1 using 1 <;> (try funext s) <;> (try simp only [id_eq]) <;> ring
  have hB : HasDerivAt (fun s : ℝ => 2 * (1 - s) / κ - 1) (-2 / κ) u := by
    convert ((hasDerivAt_id u).const_mul (-2 / κ)).add_const (2 / κ - 1) using 1 <;> (try funext s) <;> (try simp only [id_eq]) <;> ring
  have hf := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp)
  convert ((hf _).hasDerivAt.comp u hA).mul ((hf _).hasDerivAt.comp u hB) using 1
  all_goals
    try funext s
    dsimp only [indexCutoff, Function.comp_def, Pi.mul_apply, id_eq] <;> ring

theorem indexCutoff_derivative_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ κ : ℝ, 0 < κ → ∀ u : ℝ, |deriv (indexCutoff κ) u| ≤ M / κ := by
  obtain ⟨B, hB, hbound⟩ := smoothTransition_derivative_bounded
  refine ⟨4 * B, mul_pos (by norm_num) hB, ?_⟩
  intro κ hκ u
  let c := 2 / κ
  have hc : 0 ≤ c := (div_pos (by norm_num) hκ).le
  have hfabs (x : ℝ) : |Real.smoothTransition x| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hfirst : |c * deriv Real.smoothTransition (2 * u / κ - 1) *
      Real.smoothTransition (2 * (1 - u) / κ - 1)| ≤ c * B := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hbound _) hc) (hfabs _)
      (abs_nonneg _) (mul_nonneg hc hB.le)).trans_eq (mul_one _)
  have hsecond : |c * Real.smoothTransition (2 * u / κ - 1) *
      deriv Real.smoothTransition (2 * (1 - u) / κ - 1)| ≤ c * B := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    have H : c * |Real.smoothTransition (2 * u / κ - 1)| *
        |deriv Real.smoothTransition (2 * (1 - u) / κ - 1)| ≤ (c * 1) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hfabs (2 * u / κ - 1)) hc)
        (hbound (2 * (1 - u) / κ - 1)) (abs_nonneg _) (mul_nonneg hc zero_le_one)
    simpa only [mul_one] using H
  rw [(indexCutoff_hasDerivAt κ u).deriv]
  calc
    _ ≤ |c * deriv Real.smoothTransition (2 * u / κ - 1) *
        Real.smoothTransition (2 * (1 - u) / κ - 1)| +
        |c * Real.smoothTransition (2 * u / κ - 1) *
        deriv Real.smoothTransition (2 * (1 - u) / κ - 1)| := abs_sub _ _
    _ ≤ c * B + c * B := add_le_add hfirst hsecond
    _ = _ := by dsimp only [c]; ring

def indexCutoffRatio (κ u : ℝ) : ℝ := indexCutoff κ u / u

theorem indexCutoffRatio_contDiff {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ ∞ (indexCutoffRatio κ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u = 0
  · subst u
    have heq : indexCutoffRatio κ =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds (half_pos hκ)] with v hv
      simp only [indexCutoffRatio, indexCutoff_zero_left hκ hv.le, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact (indexCutoff_contDiff κ).contDiffAt.div contDiffAt_id hu

theorem indexCutoffRatio_mul {κ : ℝ} (hκ : 0 < κ) (u : ℝ) :
    u * indexCutoffRatio κ u = indexCutoff κ u := by
  by_cases hu : u = 0
  · subst u
    simp only [zero_mul, indexCutoff_zero_left hκ (half_pos hκ).le]
  · dsimp only [indexCutoffRatio]
    field_simp

theorem indexCutoffRatio_endpoints {κ : ℝ} (hκ : 0 < κ) :
    indexCutoffRatio κ 0 = 0 ∧ indexCutoffRatio κ 1 = 0 := by
  constructor
  · simp [indexCutoffRatio]
  · have hz : indexCutoff κ 1 = 0 := indexCutoff_zero_right (u := 1) hκ (by linarith)
    simp only [indexCutoffRatio, hz, zero_div]

end Yau.NodeProofs.C01Aux
