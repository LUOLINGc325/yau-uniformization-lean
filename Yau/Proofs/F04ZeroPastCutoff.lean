import Yau.LeafProofs.L16InitialTimeCutoff

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

/-- The transition begins strictly after zero, so multiplying a compact test
 gives a test whose support stays inside the positive-time slab. -/
def zeroPastCutoff (δ t : ℝ) : ℝ := Real.smoothTransition (t / δ - 1)

theorem zeroPastCutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (zeroPastCutoff δ) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.div_const δ).sub contDiff_const)

theorem zeroPastCutoff_range (δ t : ℝ) :
    0 ≤ zeroPastCutoff δ t ∧ zeroPastCutoff δ t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem zeroPastCutoff_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    zeroPastCutoff δ t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith [(div_le_one hδ).mpr ht]

theorem zeroPastCutoff_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    zeroPastCutoff δ t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith [(le_div_iff₀ hδ).mpr ht]

theorem zeroPastCutoff_deriv (δ t : ℝ) :
    deriv (zeroPastCutoff δ) t = deriv Real.smoothTransition (t / δ - 1) / δ := by
  have hAffine := ((hasDerivAt_id t).div_const δ).sub_const 1
  have hSmooth : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hComp := (hSmooth.differentiable (by norm_num)
    (t / δ - 1)).hasDerivAt.comp t hAffine
  have hResult : HasDerivAt (zeroPastCutoff δ)
      (deriv Real.smoothTransition (t / δ - 1) * (1 / δ)) t := hComp
  simpa only [div_eq_mul_inv, one_mul] using hResult.deriv

theorem zeroPastCutoff_deriv_zero {δ t : ℝ} (hδ : 0 < δ)
    (ht : t < δ ∨ 2 * δ < t) : deriv (zeroPastCutoff δ) t = 0 := by
  rcases ht with ht | ht
  · have he : zeroPastCutoff δ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact zeroPastCutoff_zero hδ hs.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : zeroPastCutoff δ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact zeroPastCutoff_one hδ hs.le
    simpa only [deriv_const] using he.deriv_eq

/-- The factor 1/delta is absorbed by the original linear initial growth.
The bound is independent of delta and is suitable for dominated convergence. -/
theorem zeroPastCutoff_growth_error_bound
    {D K δ t v : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hDeriv : ∀ s, |deriv Real.smoothTransition s| ≤ D)
    (hv : |v| ≤ K * t) :
    |deriv (zeroPastCutoff δ) t * v| ≤ 2 * D * K := by
  by_cases ht : t < δ ∨ 2 * δ < t
  · rw [zeroPastCutoff_deriv_zero hδ ht, zero_mul, abs_zero]
    positivity
  · have ht2 : t ≤ 2 * δ := le_of_not_gt (fun h => ht (Or.inr h))
    rw [abs_mul, zeroPastCutoff_deriv, abs_div, abs_of_pos hδ]
    calc
      _ ≤ (D / δ) * (K * (2 * δ)) :=
        mul_le_mul ((div_le_div_iff_of_pos_right hδ).mpr (hDeriv _))
          (hv.trans (mul_le_mul_of_nonneg_left ht2 hK)) (abs_nonneg _) (by positivity)
      _ = 2 * D * K := by field_simp [ne_of_gt hδ] <;> ring

theorem zeroPastCutoff_eventually_one {t : ℝ} (ht : 0 < t) :
    ∀ᶠ j : ℕ in atTop, zeroPastCutoff (1 / ((j : ℝ) + 1)) t = 1 ∧
      deriv (zeroPastCutoff (1 / ((j : ℝ) + 1))) t = 0 := by
  have hlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually (Iio_mem_nhds (show (0 : ℝ) < t / 2 by positivity))] with j hj
  have hδ : 0 < 1 / ((j : ℝ) + 1) := by positivity
  have hsmall : 2 * (1 / ((j : ℝ) + 1)) < t := by linarith
  exact ⟨zeroPastCutoff_one hδ hsmall.le, zeroPastCutoff_deriv_zero hδ (Or.inr hsmall)⟩

end Yau.F04Proof
