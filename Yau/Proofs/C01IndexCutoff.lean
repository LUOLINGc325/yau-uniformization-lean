import Yau.Proofs.C01ScalarDistanceGrowth
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A genuine smooth endpoint cutoff for the index-form argument.
It vanishes on neighborhoods of both endpoints and is exactly one in
the middle of the unit interval. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux


def indexCutoff (κ u : ℝ) : ℝ :=
  Real.smoothTransition (2 * u / κ - 1) *
    Real.smoothTransition (2 * (1 - u) / κ - 1)

theorem indexCutoff_contDiff (κ : ℝ) : ContDiff ℝ ∞ (indexCutoff κ) := by
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem indexCutoff_nonneg (κ u : ℝ) : 0 ≤ indexCutoff κ u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem indexCutoff_le_one (κ u : ℝ) : indexCutoff κ u ≤ 1 := by
  exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem indexCutoff_zero_left {κ u : ℝ} (hκ : 0 < κ) (hu : u ≤ κ / 2) :
    indexCutoff κ u = 0 := by
  have harg : 2 * u / κ - 1 ≤ 0 := by
    have H : 2 * u / κ ≤ 1 := (div_le_one hκ).mpr (by linarith)
    linarith
  simp only [indexCutoff, Real.smoothTransition.zero_of_nonpos harg, zero_mul]

theorem indexCutoff_zero_right {κ u : ℝ} (hκ : 0 < κ) (hu : 1 - κ / 2 ≤ u) :
    indexCutoff κ u = 0 := by
  have harg : 2 * (1 - u) / κ - 1 ≤ 0 := by
    have H : 2 * (1 - u) / κ ≤ 1 := (div_le_one hκ).mpr (by linarith)
    linarith
  simp only [indexCutoff, Real.smoothTransition.zero_of_nonpos harg, mul_zero]

theorem indexCutoff_one_middle {κ u : ℝ} (hκ : 0 < κ)
    (hu : κ ≤ u) (hu' : u ≤ 1 - κ) : indexCutoff κ u = 1 := by
  have harg₁ : 1 ≤ 2 * u / κ - 1 := by
    have H : 2 ≤ 2 * u / κ := (le_div_iff₀ hκ).mpr (by linarith)
    linarith
  have harg₂ : 1 ≤ 2 * (1 - u) / κ - 1 := by
    have H : 2 ≤ 2 * (1 - u) / κ := (le_div_iff₀ hκ).mpr (by linarith)
    linarith
  simp only [indexCutoff, Real.smoothTransition.one_of_one_le harg₁,
    Real.smoothTransition.one_of_one_le harg₂, mul_one]

theorem smoothTransition_derivative_bounded :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, |deriv Real.smoothTransition u| ≤ B := by
  have hc : Continuous (fun u => |deriv Real.smoothTransition u|) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp)).abs
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 2)).bddAbove_image hc.continuousOn
  let B := max B₀ 1
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro u
  by_cases hu : u ∈ Set.Icc (-1 : ℝ) 2
  · exact (hB₀ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
  · have hd : deriv Real.smoothTransition u = 0 := by
      by_cases hu₁ : -1 ≤ u
      · have hu₂ : 2 < u := lt_of_not_ge (fun h => hu ⟨hu₁, h⟩)
        have heq : Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
          filter_upwards [isOpen_Ioi.mem_nhds (show 1 < u by linarith)] with v hv
          exact Real.smoothTransition.one_of_one_le hv.le
        rw [heq.deriv_eq]
        exact deriv_const _ _
      · have hu₂ : u < -1 := lt_of_not_ge hu₁
        have heq : Real.smoothTransition =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
          filter_upwards [isOpen_Iio.mem_nhds (show u < 0 by linarith)] with v hv
          exact Real.smoothTransition.zero_of_nonpos hv.le
        rw [heq.deriv_eq]
        exact deriv_const _ _
    rw [hd, abs_zero]
    exact (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le

end Yau.NodeProofs.C01Aux
