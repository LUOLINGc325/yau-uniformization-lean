import Yau.Proofs.P04PoleTranslation

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- Finite singular weighted norm forces the zeroth coefficient to vanish.
Only continuity at the pole is used, and no log value there is assigned. -/
theorem pole_weight_forces_value_zero {n : ℕ} (hn : 0 < n) (z₀ : ComplexVector n)
    {ρ : ℝ} (hρ : 0 < ρ) (b : ComplexVector n → ℂ) (Φ : ComplexVector n → ℝ)
    (hb : ContinuousAt b z₀) (hΦ : ContinuousAt Φ z₀)
    (hfinite : (∫⁻ z in Metric.ball z₀ ρ,
      ENNReal.ofReal (‖b z‖^2*Real.exp (-Φ z)*‖z-z₀‖^(-2*((n : ℝ)+1))) ∂lebesgueC n) < ⊤) :
    b z₀=0 := by
  by_contra hne
  let w : ComplexVector n → ℝ := fun z => ‖b z‖^2*Real.exp (-Φ z)
  have hw : ContinuousAt w z₀ :=
    (hb.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp hΦ.neg)
  have hwp : 0 < w z₀ := mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)) (Real.exp_pos _)
  let δ := w z₀/2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδw : δ < w z₀ := by dsimp only [δ]; linarith
  have hnear : ∀ᶠ z in 𝓝 z₀, δ < w z := hw.eventually (Ioi_mem_nhds hδw)
  obtain ⟨η,hη,hηbound⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min η ρ
  have hr : 0 < r := lt_min hη hρ
  have hsubη : Metric.ball z₀ r ⊆ Metric.ball z₀ η := Metric.ball_subset_ball (min_le_left _ _)
  have hsubρ : Metric.ball z₀ r ⊆ Metric.ball z₀ ρ := Metric.ball_subset_ball (min_le_right _ _)
  let P : ComplexVector n → ℝ := fun z => ‖z-z₀‖^(-2*((n : ℝ)+1))
  have hP (z : ComplexVector n) : 0 ≤ P z := Real.rpow_nonneg (norm_nonneg _) _
  have hδinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hfinP : (∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal (P z) ∂lebesgueC n) < ⊤ := by
    calc
      _ ≤ ∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal (δ⁻¹*(w z*P z)) ∂lebesgueC n := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
        apply ENNReal.ofReal_le_ofReal
        have hW : δ ≤ w z := (hηbound (hsubη hz)).le
        have hscale : 1 ≤ δ⁻¹*w z := by
          calc
            _ = δ⁻¹*δ := (inv_mul_cancel₀ hδ.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left hW hδinv
        simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hscale (hP z)
      _ = ENNReal.ofReal δ⁻¹*∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal (w z*P z) ∂lebesgueC n := by
        simp only [ENNReal.ofReal_mul hδinv]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal δ⁻¹*∫⁻ z in Metric.ball z₀ ρ, ENNReal.ofReal (w z*P z) ∂lebesgueC n := by
        gcongr
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite
  have hmP : Measurable P :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).measurable.pow_const _
  have hInt : IntegrableOn P (Metric.ball z₀ r) (lebesgueC n) :=
    ⟨hmP.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP)).mpr hfinP⟩
  exact norm_pole_not_integrableOn_at hn z₀ hr hInt

end Yau.Proofs.P04Aux
