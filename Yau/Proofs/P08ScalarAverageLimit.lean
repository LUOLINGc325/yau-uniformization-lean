import Yau.Proofs.P08RegularizedLog

/-! Fatou removes the positive canonical regularization after the actual
zero set has been proved null. No signed logarithmic integral is passed to a limit. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Yau.NodeProofs.P08Aux.ScalarAverage

theorem regularized_weight_lintegral_limit {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q R χ : α → ℝ) (hq : Measurable q)
    (hR : Measurable R) (hχ : Measurable χ) (hzero : μ {x | q x = 0} = 0)
    (D : ℝ≥0∞)
    (hbound : ∀ j : ℕ, (∫⁻ x, ENNReal.ofReal
      (χ x * (q x / (q x + logRegularizationParameter j) * R x)) ∂μ) ≤ D) :
    (∫⁻ x, ENNReal.ofReal (χ x * R x) ∂μ) ≤ D := by
  have hm (j : ℕ) : Measurable (fun x => ENNReal.ofReal
      (χ x * (q x / (q x + logRegularizationParameter j) * R x))) :=
    ENNReal.measurable_ofReal.comp (hχ.mul ((hq.div (hq.add_const _)).mul hR))
  have hae : ∀ᵐ x ∂μ, q x ≠ 0 := by
    exact measure_eq_zero_iff_ae_notMem.mp hzero
  have heq : (fun x => ENNReal.ofReal (χ x * R x)) =ᵐ[μ]
      fun x => liminf (fun j => ENNReal.ofReal
        (χ x * (q x / (q x + logRegularizationParameter j) * R x))) atTop := by
    filter_upwards [hae] with x hx
    have hden : Tendsto (fun j => q x + logRegularizationParameter j) atTop (𝓝 (q x)) := by
      simpa only [add_zero] using tendsto_const_nhds.add logRegularizationParameter_tendsto
    have hr : Tendsto (fun j => q x / (q x + logRegularizationParameter j)) atTop (𝓝 1) := by
      have hnum : Tendsto (fun _ : ℕ => q x) atTop (𝓝 (q x)) := tendsto_const_nhds
      have ht := hnum.div hden hx
      rw [div_self hx] at ht
      convert ht using 1
    have ht : Tendsto (fun j => ENNReal.ofReal
        (χ x * (q x / (q x + logRegularizationParameter j) * R x))) atTop
          (𝓝 (ENNReal.ofReal (χ x * R x))) := by
      simpa only [Function.comp_def, one_mul] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul (hr.mul tendsto_const_nhds))
    exact ht.liminf_eq.symm
  calc
    _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal
        (χ x * (q x / (q x + logRegularizationParameter j) * R x))) atTop ∂μ :=
      lintegral_congr_ae heq
    _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal
        (χ x * (q x / (q x + logRegularizationParameter j) * R x)) ∂μ) atTop :=
      lintegral_liminf_le hm
    _ ≤ D := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end Yau.NodeProofs.P08Aux.ScalarAverage
