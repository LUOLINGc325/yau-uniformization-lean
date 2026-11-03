import Yau.Proofs.F04SmoothPositiveScalar

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

theorem smoothPositive_increment {δ s : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) :
    smoothPositive δ s = smoothPositive δ δ + (s - δ) := by
  have hc : Continuous (fun q : ℝ => Real.smoothTransition (q / δ)) :=
    Real.smoothTransition.continuous.comp (continuous_id.div_const δ)
  have hi : (∫ q in δ..s, Real.smoothTransition (q / δ)) = s - δ := by
    have he : (∫ q in δ..s, Real.smoothTransition (q / δ)) = ∫ _q in δ..s, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hs] at hq
      exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).mpr (by simpa using hq.1))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using he
  have ha := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 δ)
    (hc.intervalIntegrable (μ := volume) δ s)
  rw [hi] at ha
  exact ha.symm

theorem smoothPositive_error_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    |smoothPositive δ s - max s 0| ≤ δ := by
  rcases le_total s 0 with hs | hs
  · rw [smoothPositive_of_nonpos hδ hs, max_eq_right hs, sub_self, abs_zero]
    exact hδ.le
  · have hb := smoothPositive_bounds hδ s
    rw [max_eq_left hs] at hb ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hb.2)]
    rcases le_total s δ with hsd | hds
    · linarith
    · rw [smoothPositive_increment hδ hds]
      have hbd := (smoothPositive_bounds hδ δ).1
      linarith

theorem smoothPositive_error_le_pos {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    |smoothPositive δ s - max s 0| ≤ max s 0 := by
  have hb := smoothPositive_bounds hδ s
  rw [abs_of_nonpos (sub_nonpos.mpr hb.2)]
  linarith

theorem smoothPositive_tendsto (s : ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => smoothPositive (δ j) s) atTop (𝓝 (max s 0)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun j => smoothPositive (δ j) s - max s 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => by simpa only [Real.norm_eq_abs] using smoothPositive_error_le (hδ j) s)
    exact hlim
  simpa only [norm_zero] using hz.norm

theorem smoothPositive_deriv_tendsto (s : ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => deriv (smoothPositive (δ j)) s) atTop (𝓝 (if 0 < s then 1 else 0)) := by
  by_cases hs : 0 < s
  · rw [ite_eq_left hs]
    have he : (fun j => deriv (smoothPositive (δ j)) s) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [hlim.eventually (gt_mem_nhds hs)] with j hj
      rw [smoothPositive_deriv]
      exact Real.smoothTransition.one_of_one_le ((le_div_iff₀ (hδ j)).mpr (by linarith))
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  · rw [ite_eq_right hs]
    simpa only [smoothPositive_deriv_of_nonpos (hδ _) (le_of_not_gt hs)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Yau.F04Proof
