import Yau.Geometry.Basic

open scoped Topology ENNReal
open MeasureTheory Set Filter Metric

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

def planarPuncturedDisc (R : ℝ) : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < R}

theorem planarPuncturedDisc_isOpen (R : ℝ) : IsOpen (planarPuncturedDisc R) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

/-- Finite area L² mass has vanishing tails at the puncture. -/
theorem holomorphic_l2_tail_tendsto {q : ℕ} (R : ℝ) (F : ℂ → ComplexVector q)
    (hF : DifferentiableOn ℂ F (planarPuncturedDisc R))
    (hL2 : (∫⁻ z in planarPuncturedDisc R, ENNReal.ofReal (‖F z‖ ^ 2) ∂volume) < ⊤) :
    Tendsto (fun ρ : ℝ => ∫⁻ w in ball (0 : ℂ) ρ,
      ENNReal.ofReal (‖F w‖ ^ 2) ∂(volume.restrict (planarPuncturedDisc R)))
      (𝓝 0) (𝓝 0) := by
  let μ : Measure ℂ := volume.restrict (planarPuncturedDisc R)
  let g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖F w‖ ^ 2)
  have hm : AEMeasurable g μ :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hF.continuousOn.norm.pow 2)).aemeasurable
      (planarPuncturedDisc_isOpen R).measurableSet
  have hi : ∀ᶠ ρ : ℝ in 𝓝 0, AEMeasurable ((ball (0 : ℂ) ρ).indicator g) μ :=
    Filter.Eventually.of_forall (fun ρ => hm.indicator measurableSet_ball)
  have hb : ∀ᶠ ρ : ℝ in 𝓝 0, ∀ᵐ w ∂μ, (ball (0 : ℂ) ρ).indicator g w ≤ g w := by
    apply Filter.Eventually.of_forall
    intro ρ
    apply Filter.Eventually.of_forall
    intro w
    by_cases hw : w ∈ ball (0 : ℂ) ρ <;> simp [hw]
  have hlim : ∀ᵐ w ∂μ, Tendsto (fun ρ : ℝ => (ball (0 : ℂ) ρ).indicator g w) (𝓝 0) (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem (planarPuncturedDisc_isOpen R).measurableSet] with w hw
    apply tendsto_const_nhds.congr'
    filter_upwards [Iio_mem_nhds hw.1] with ρ hρ
    have hnot : w ∉ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff]
      exact not_lt_of_ge hρ.le
    simp [hnot]
  have ht := tendsto_lintegral_filter_of_dominated_convergence' g hi hb hL2.ne hlim
  simpa only [lintegral_indicator measurableSet_ball, lintegral_zero] using ht

end Yau.Proofs.D03Aux
