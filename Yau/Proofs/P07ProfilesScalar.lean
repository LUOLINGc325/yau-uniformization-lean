import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The fixed scalar profile and quantitative derivative bounds, independent
of the manifold, heat time, scale and evaluation point. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P07Aux

def radialProfile (s : ℝ) : ℝ := Real.smoothTransition ((s - 1) / 3)

theorem radialProfile_contDiff : ContDiff ℝ ∞ radialProfile :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const 3)

theorem radialProfile_monotone : Monotone radialProfile := by
  intro s t hst
  apply Real.smoothTransition.monotone
  linarith

theorem radialProfile_mem (s : ℝ) : radialProfile s ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem radialProfile_zero (s : ℝ) (hs : s ≤ 1) : radialProfile s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialProfile_one (s : ℝ) (hs : 4 ≤ s) : radialProfile s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem derivs_zero_of_locally_constant {f : ℝ → ℝ} {x c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  have h' : deriv f =ᶠ[𝓝 x] fun _ => 0 := by simpa using h.deriv
  exact ⟨by simpa using h.deriv_eq, by simpa using h'.deriv_eq⟩

theorem exists_plateau_derivative_bounds
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a b c0 c1 : ℝ)
    (hleft : ∀ s, s ≤ a → f s = c0) (hright : ∀ s, b ≤ s → f s = c1) :
    ∃ A1 A2 : ℝ, 0 < A1 ∧ 0 < A2 ∧
      ∀ s, |deriv f s| ≤ A1 ∧ |deriv (deriv f) s| ≤ A2 := by
  have hf' : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hf').2
  have hI : IsCompact (Icc a b) := isCompact_Icc
  obtain ⟨B1, hB1⟩ := hI.bddAbove_image hf'.continuous.abs.continuousOn
  obtain ⟨B2, hB2⟩ := hI.bddAbove_image hf''.continuous.abs.continuousOn
  refine ⟨max B1 0 + 1, max B2 0 + 1, by positivity, by positivity, ?_⟩
  intro s
  by_cases hsa : s < a
  · have hg : f =ᶠ[𝓝 s] fun _ => c0 := by
      filter_upwards [Iio_mem_nhds hsa] with y hy
      change y < a at hy
      exact hleft y hy.le
    obtain ⟨hd1, hd2⟩ := derivs_zero_of_locally_constant hg
    rw [hd1, hd2, abs_zero]
    constructor <;> positivity
  · by_cases hsb : b < s
    · have hg : f =ᶠ[𝓝 s] fun _ => c1 := by
        filter_upwards [Ioi_mem_nhds hsb] with y hy
        change b < y at hy
        exact hright y hy.le
      obtain ⟨hd1, hd2⟩ := derivs_zero_of_locally_constant hg
      rw [hd1, hd2, abs_zero]
      constructor <;> positivity
    · have hs : s ∈ Icc a b := ⟨le_of_not_gt hsa, le_of_not_gt hsb⟩
      exact ⟨(hB1 ⟨s, hs, rfl⟩).trans (by linarith [le_max_left B1 0]),
        (hB2 ⟨s, hs, rfl⟩).trans (by linarith [le_max_left B2 0])⟩

theorem radialProfile_derivative_bounds :
    ∃ A1 A2 : ℝ, 0 < A1 ∧ 0 < A2 ∧
      ∀ s, |deriv radialProfile s| ≤ A1 ∧ |deriv (deriv radialProfile) s| ≤ A2 :=
  exists_plateau_derivative_bounds radialProfile radialProfile_contDiff 1 4 0 1
    radialProfile_zero radialProfile_one

end Yau.NodeProofs.P07Aux
