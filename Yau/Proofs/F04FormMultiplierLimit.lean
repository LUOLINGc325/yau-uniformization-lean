import Yau.Proofs.F04GraphLinear

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- Dominated convergence for actual form sections.  The limit hypothesis is
weighted by the actual fixed section, so it also covers discontinuous scalar
multipliers at points where that section vanishes. -/
theorem bounded_form_multiplier_tendsto_zero
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (η : ℕ → M.Carrier → ℝ) (hηm : ∀ j, AEStronglyMeasurable (η j) μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ j x, |η j x| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => (η j x) ^ 2 * formNormSq g.form A x)
      atTop (𝓝 0)) :
    Tendsto (fun j => realizeL2Form g μ (L2FormSpace.ofSection
      (multiplyRealForm (η j) A)
      (l2RealForm_multiply_bounded g μ (η j) (hηm j) C hC (hη j) A hA)))
      atTop (𝓝 0) := by
  let B (j : ℕ) := multiplyRealForm (η j) A
  have hB (j : ℕ) : L2RealForm g.form μ (B j) :=
    l2RealForm_multiply_bounded g μ (η j) (hηm j) C hC (hη j) A hA
  have hm (j : ℕ) : AEStronglyMeasurable (formNormSq g.form (B j)) μ :=
    (formNormSq_integrable g μ (B j) (hB j)).aestronglyMeasurable
  have hd (j : ℕ) : ∀ᵐ x ∂μ,
      ‖formNormSq g.form (B j) x‖ ≤ C ^ 2 * formNormSq g.form A x := by
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (formNormSq_nonneg g.form (B j) x)]
    exact multiplyRealForm_normSq_le g.form (η j) A C hC (hη j) x
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => formNormSq g.form (B j) x) atTop (𝓝 0) := by
    simpa only [B, multiplyRealForm_normSq] using hlim
  have hi := tendsto_integral_of_dominated_convergence
    (fun x => C ^ 2 * formNormSq g.form A x) hm
    ((formNormSq_integrable g μ A hA).const_mul (C ^ 2)) hd hl
  have hs : Tendsto (fun j => ‖realizeL2Form g μ (L2FormSpace.ofSection (B j) (hB j))‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [realizeL2Form_norm_sq, L2FormSpace.toSection_ofSection, integral_zero] using hi
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- Pointwise convergence of bounded scalar multipliers acts strongly on every
fixed actual L2 form, also when the spatial measure is infinite. -/
theorem bounded_form_multiplier_tendsto_zero_of_ae
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (η : ℕ → M.Carrier → ℝ) (hηm : ∀ j, AEStronglyMeasurable (η j) μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ j x, |η j x| ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => η j x) atTop (𝓝 0)) :
    Tendsto (fun j => realizeL2Form g μ (L2FormSpace.ofSection
      (multiplyRealForm (η j) A)
      (l2RealForm_multiply_bounded g μ (η j) (hηm j) C hC (hη j) A hA)))
      atTop (𝓝 0) := by
  apply bounded_form_multiplier_tendsto_zero g μ A hA η hηm C hC hη
  filter_upwards [hlim] with x hx
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul] using (hx.pow 2).mul_const (formNormSq g.form A x)

end Yau.F04Proof
