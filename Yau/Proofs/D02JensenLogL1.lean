import Yau.Proofs.D02JensenFubini

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02JensenAux

/-- Uniform L¹ control of a logarithmic potential on a bounded evaluation
disc, for every finite positive measure with bounded support and mass. -/
theorem exists_uniform_logPotential_L1_bound (z₀ : ℂ) (R r : ℝ) (b : ℝ) (hb : 0 ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ν : Measure ℂ, IsFiniteMeasure ν →
      (∀ᵐ w ∂ν, w ∈ Metric.ball z₀ R) → (ν univ).toReal ≤ b →
      IntegrableOn (fun z ↦ ∫ w, Real.log ‖w - z‖ ∂ν) (Metric.ball z₀ r) volume ∧
      (∫ z in Metric.ball z₀ r, |∫ w, Real.log ‖w - z‖ ∂ν|) ≤ L := by
  let T := max (r + R) 1
  let k := fun z : ℂ ↦ |Real.log ‖z‖|
  have hk : Measurable k := (Real.measurable_log.comp measurable_norm).abs
  have hk0 : ∀ z, 0 ≤ k z := fun _ ↦ abs_nonneg _
  have hki : IntegrableOn k (Metric.ball 0 T) volume := (LeafProofs.L08_integrableOn_log_norm_ball T).abs
  let B := ∫ z in Metric.ball 0 T, k z
  have hB : 0 ≤ B := integral_nonneg hk0
  refine ⟨B * b, mul_nonneg hB hb, ?_⟩
  intro ν hν hνD hmass
  letI : IsFiniteMeasure ν := hν
  have hkw : ∀ w ∈ Metric.ball z₀ R,
      IntegrableOn (fun z ↦ k (w - z)) (Metric.ball z₀ r) volume ∧
        (∫ z in Metric.ball z₀ r, k (w - z)) ≤ B :=
    fun w hw ↦ integral_kernel_disc_bound hki hk0 (le_max_left _ _) hw
  have hiK := integrable_pair_kernel hk hk0 hνD hkw
  have hlog : Measurable (fun q : ℂ × ℂ ↦ Real.log ‖q.2 - q.1‖) :=
    Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm
  have hiLog : Integrable (fun q : ℂ × ℂ ↦ Real.log ‖q.2 - q.1‖)
      ((volume.restrict (Metric.ball z₀ r)).prod ν) := by
    apply hiK.mono' hlog.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q ↦ by rw [Real.norm_eq_abs]
  refine ⟨hiLog.integral_prod_left, ?_⟩
  have hle : (∫ z in Metric.ball z₀ r, |∫ w, Real.log ‖w - z‖ ∂ν|) ≤
      ∫ z in Metric.ball z₀ r, ∫ w, k (w - z) ∂ν := by
    apply integral_mono_ae hiLog.integral_prod_left.abs hiK.integral_prod_left
    exact Filter.Eventually.of_forall fun z ↦ by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun w ↦ Real.log ‖w - z‖) (μ := ν)
  exact hle.trans ((integral_pair_kernel_le hk hk0 hνD hkw).trans (mul_le_mul_of_nonneg_left hmass hB))

end Yau.NodeProofs.D02JensenAux
