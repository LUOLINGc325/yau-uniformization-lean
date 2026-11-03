import Yau.Proofs.F04FiniteMass

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

/-- A smooth positive part whose derivative is exactly zero at every
nonpositive argument, including the zero level. -/
def smoothPositive (δ s : ℝ) : ℝ := ∫ q in (0 : ℝ)..s, Real.smoothTransition (q / δ)

theorem smoothPositive_hasDerivAt (δ s : ℝ) :
    HasDerivAt (smoothPositive δ) (Real.smoothTransition (s / δ)) s := by
  have hc : Continuous (fun q : ℝ => Real.smoothTransition (q / δ)) :=
    Real.smoothTransition.continuous.comp (continuous_id.div_const δ)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := volume) 0 s)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem smoothPositive_deriv (δ s : ℝ) :
    deriv (smoothPositive δ) s = Real.smoothTransition (s / δ) :=
  (smoothPositive_hasDerivAt δ s).deriv

theorem smoothPositive_contDiff (δ : ℝ) : ContDiff ℝ ∞ (smoothPositive δ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (smoothPositive_hasDerivAt δ s).differentiableAt, ?_⟩
  simp only [show deriv (smoothPositive δ) = (fun s => Real.smoothTransition (s / δ))
    from funext (smoothPositive_deriv δ)]
  exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)

theorem smoothPositive_zero (δ : ℝ) : smoothPositive δ 0 = 0 := by
  simp only [smoothPositive, intervalIntegral.integral_same]

theorem smoothPositive_deriv_bounds (δ s : ℝ) :
    0 ≤ deriv (smoothPositive δ) s ∧ deriv (smoothPositive δ) s ≤ 1 := by
  rw [smoothPositive_deriv]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem smoothPositive_lipschitz (δ : ℝ) : LipschitzWith 1 (smoothPositive δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((smoothPositive_contDiff δ).differentiable (by simp))
  intro s
  have hd := smoothPositive_deriv_bounds δ s
  exact_mod_cast (show |deriv (smoothPositive δ) s| ≤ 1 by rw [abs_of_nonneg hd.1]; exact hd.2)

theorem smoothPositive_of_nonpos {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) :
    smoothPositive δ s = 0 := by
  unfold smoothPositive
  have hi : (∫ q in (0 : ℝ)..s, Real.smoothTransition (q / δ)) = ∫ _q in (0 : ℝ)..s, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_ge hs] at hq
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hq.2 hδ.le)
  rw [hi, intervalIntegral.integral_zero]

theorem smoothPositive_deriv_of_nonpos {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : s ≤ 0) :
    deriv (smoothPositive δ) s = 0 := by
  rw [smoothPositive_deriv]
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hs hδ.le)

theorem smoothPositive_bounds {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    0 ≤ smoothPositive δ s ∧ smoothPositive δ s ≤ max s 0 := by
  rcases le_total s 0 with hs | hs
  · rw [smoothPositive_of_nonpos hδ hs, max_eq_right hs]
    exact ⟨le_rfl, le_rfl⟩
  · have hc : Continuous (fun q : ℝ => Real.smoothTransition (q / δ)) :=
      Real.smoothTransition.continuous.comp (continuous_id.div_const δ)
    refine ⟨intervalIntegral.integral_nonneg_of_forall hs (fun q => Real.smoothTransition.nonneg _), ?_⟩
    rw [max_eq_left hs]
    have hi := intervalIntegral.integral_mono_on hs (hc.intervalIntegrable (μ := volume) 0 s)
      (continuous_const.intervalIntegrable (μ := volume) 0 s) (fun q _ => Real.smoothTransition.le_one (q / δ))
    simpa only [smoothPositive, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hi

end Yau.F04Proof
