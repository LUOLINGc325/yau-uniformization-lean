import Yau.LeafProofs.L19KernelRegularizedCore

/-! A genuine nonnegative Fatou bound, before total kernel integrability is known. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Uniform bounds on genuine integrals of nonnegative approximants
force both integrability and the same bound on their measurable limit. -/
theorem integrable_nonnegative_fatou_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℕ → X → ℝ} {f : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ j, Integrable (F j) μ) (hF0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ F j x)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)))
    (hbound : ∀ j, (∫ x, F j x ∂μ) ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C := by
  have hnorm (j : ℕ) : (∫⁻ x, ‖F j x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (F j x) ∂μ := lintegral_congr_ae
        ((hF0 j).mono fun x hx => Real.enorm_of_nonneg hx)
      _ = ENNReal.ofReal (∫ x, F j x ∂μ) := (ofReal_integral_eq_lintegral_ofReal (hF j) (hF0 j)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hbound j)
  have hFat : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, liminf (fun j => ‖F j x‖ₑ) atTop ∂μ :=
        (lintegral_congr_ae (hlim.mono fun x hx => hx.enorm.liminf_eq)).symm
      _ ≤ liminf (fun j => ∫⁻ x, ‖F j x‖ₑ ∂μ) atTop :=
        lintegral_liminf_le' (fun j => (hF j).aestronglyMeasurable.enorm)
      _ ≤ _ := liminf_le_of_frequently_le' (Filter.Frequently.of_forall hnorm)
  have hi : Integrable f μ := ⟨hf, lt_of_le_of_lt hFat ENNReal.ofReal_lt_top⟩
  refine ⟨hi, ?_⟩
  have hFat' : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    convert hFat using 1
    exact (lintegral_congr_ae (hf0.mono fun x hx => Real.enorm_of_nonneg hx)).symm
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf]
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hFat'

end Yau.LeafProofs.L19Aux
