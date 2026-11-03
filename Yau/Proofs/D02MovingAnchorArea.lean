import Yau.Proofs.D02GoodAngles
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The moving anchors are actual measurable subsets of one fixed compact
annulus. Their planar area is computed from the same good radial angles. -/

open scoped ENNReal
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

theorem polarRay_arg {r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-Real.pi) Real.pi) :
    Complex.arg (polarRay r θ) = θ := by
  have h := congrArg Prod.snd (Complex.polarCoord.right_inv
    (show (r, θ) ∈ Complex.polarCoord.target from ⟨hr, hθ⟩))
  simpa only [Complex.polarCoord_apply, polarRay] using h

def anchorAnnulus (Θ : Set ℝ) : Set ℂ :=
  {z | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 3 / 4 ∧ Complex.arg z ∈ Θ}

theorem anchorAnnulus_measurable {Θ : Set ℝ} (hΘ : MeasurableSet Θ) :
    MeasurableSet (anchorAnnulus Θ) :=
  (measurableSet_lt measurable_const continuous_norm.measurable).inter
    ((measurableSet_lt continuous_norm.measurable measurable_const).inter
      (hΘ.preimage Complex.measurable_arg))

theorem anchorAnnulus_subset_compactAnnulus (Θ : Set ℝ) :
    anchorAnnulus Θ ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le⟩

theorem anchorCompactAnnulus_isCompact :
    IsCompact {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} := by
  apply (isCompact_closedBall (0 : ℂ) (3 / 4)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2

theorem anchor_radial_mass :
    (∫⁻ r in Ioo (1 / 2 : ℝ) (3 / 4), ENNReal.ofReal r) = ENNReal.ofReal (5 / 32 : ℝ) := by
  have hi : IntegrableOn (fun r : ℝ => r) (Ioo (1 / 2 : ℝ) (3 / 4)) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4),
      integral_id]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (by norm_num : (0 : ℝ) < 1 / 2).le.trans hr.1.le

/-- Exact planar area of the moving annulus, including its fixed Jacobian factor. -/
theorem anchorAnnulus_volume {Θ : Set ℝ} (hΘ : MeasurableSet Θ)
    (hΘsub : Θ ⊆ Ioo (-Real.pi) Real.pi) :
    volume (anchorAnnulus Θ) = ENNReal.ofReal (5 / 32 : ℝ) * volume Θ := by
  classical
  let S := anchorAnnulus Θ
  have hS : MeasurableSet S := anchorAnnulus_measurable hΘ
  let Q : ℂ → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hQ : Measurable Q := measurable_const.indicator hS
  have hformula := annulus_lintegral_polar Q hQ
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 3 / 4)
  have hlhs : (∫⁻ z in {z : ℂ | (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 3 / 4}, Q z) = volume S := by
    rw [lintegral_indicator hS]
    simp only [lintegral_one, Measure.restrict_apply_univ]
    rw [Measure.restrict_apply hS]
    congr 1
    apply inter_eq_left.mpr
    intro z hz
    exact ⟨hz.1, hz.2.1⟩
  have hrhs : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo (1 / 2 : ℝ) (3 / 4),
      ENNReal.ofReal r * Q (polarRay r θ)) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, Θ.indicator (fun _ => ENNReal.ofReal (5 / 32 : ℝ)) θ := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    by_cases hmem : θ ∈ Θ
    · rw [indicator_of_mem hmem, ← anchor_radial_mass]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1
      have hpt : polarRay r θ ∈ S := by
        exact ⟨by simpa [polarRay_norm, abs_of_pos hr0] using hr.1,
          by simpa [polarRay_norm, abs_of_pos hr0] using hr.2,
          by rwa [polarRay_arg hr0 hθ]⟩
      simp only [Q, indicator_of_mem hpt, mul_one]
    · rw [indicator_of_notMem hmem]
      calc
        _ = ∫⁻ _r in Ioo (1 / 2 : ℝ) (3 / 4), (0 : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 2).trans hr.1
          have hpt : polarRay r θ ∉ S := by
            intro h
            apply hmem
            have hm := h.2.2
            rwa [polarRay_arg hr0 hθ] at hm
          simp only [Q, indicator_of_notMem hpt, mul_zero]
        _ = 0 := by simp
  rw [hlhs, hrhs, lintegral_indicator hΘ] at hformula
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.restrict_apply hΘ,
    inter_eq_left.mpr hΘsub] using hformula

theorem disc_movingAnchorArea {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (A : ℝ)
    (harea : discArea g.form f ≤ ENNReal.ofReal A) :
    let S := anchorAnnulus (goodAngles (discEnergyDensity g.form f) A)
    MeasurableSet S ∧ ENNReal.ofReal (5 * Real.pi / 32) ≤ volume S ∧
      S ⊆ {z : ℂ | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 4} := by
  obtain ⟨hΘ, hvol, _⟩ := disc_goodAngles g hf A harea
  refine ⟨anchorAnnulus_measurable hΘ, ?_, anchorAnnulus_subset_compactAnnulus _⟩
  rw [anchorAnnulus_volume hΘ inter_subset_left]
  have he : ENNReal.ofReal (5 * Real.pi / 32) =
      ENNReal.ofReal (5 / 32 : ℝ) * ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5 / 32)]
    congr 1
    ring
  rw [he]
  gcongr

end Yau.NodeProofs.D02Aux
