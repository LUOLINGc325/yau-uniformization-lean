import Yau.Proofs.D03PlanarJets
import Yau.Proofs.D03PlanarTail

open scoped Topology ENNReal
open MeasureTheory Set Filter Metric Asymptotics

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau

/-- The shrinking-area estimate rules out even a simple pole. -/
theorem holomorphic_l2_norm_mul_tendsto {q : ℕ} (R : ℝ) (hR : 0 < R)
    (F : ℂ → ComplexVector q) (hF : DifferentiableOn ℂ F (planarPuncturedDisc R))
    (hL2 : (∫⁻ z in planarPuncturedDisc R, ENNReal.ofReal (‖F z‖ ^ 2) ∂volume) < ⊤) :
    Tendsto (fun z : ℂ => ‖z‖ * ‖F z‖) (𝓝[≠] 0) (𝓝 0) := by
  let T : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ w in ball (0 : ℂ) ρ ∩ planarPuncturedDisc R,
    ENNReal.ofReal (‖F w‖ ^ 2) ∂volume
  have hT : Tendsto T (𝓝 0) (𝓝 0) := by
    simpa only [T, Measure.restrict_restrict measurableSet_ball] using
      holomorphic_l2_tail_tendsto R F hF hL2
  have hn : Tendsto (fun z : ℂ => 2 * ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using
      ((continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).const_mul (2 : ℝ)
  have hreal : Tendsto (fun z : ℂ => (T (2 * ‖z‖)).toReal) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hT.comp hn)
  have hsqrt : Tendsto (fun z : ℂ => Real.sqrt ((4 / Real.pi) * (T (2 * ‖z‖)).toReal))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hreal.const_mul (4 / Real.pi))
  have hevent : ∀ᶠ z : ℂ in 𝓝[≠] 0, ‖z‖ < R / 2 ∧ z ≠ 0 := by
    filter_upwards [show ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ ball 0 (R / 2) from
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (by positivity)), self_mem_nhdsWithin] with z hz hnz
    exact ⟨by simpa only [mem_ball_zero_iff] using hz, hnz⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun z => mul_nonneg (norm_nonneg z) (norm_nonneg (F z)))) _ hsqrt
  filter_upwards [hevent] with z hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz.2
  let U : Set ℂ := ball 0 (2 * ‖z‖) ∩ planarPuncturedDisc R
  have hU : IsOpen U := isOpen_ball.inter (planarPuncturedDisc_isOpen R)
  have hball : closedBall z (‖z‖ / 2) ⊆ U := by
    intro w hw
    have hw' := mem_closedBall.mp hw
    have hupper := dist_triangle w z (0 : ℂ)
    have hlower := dist_triangle z w (0 : ℂ)
    simp only [dist_zero_right] at hupper hlower
    rw [dist_comm z w] at hlower
    have hwpos : 0 < ‖w‖ := by linarith
    have hwsmall : ‖w‖ < 2 * ‖z‖ := by linarith
    have hwR : ‖w‖ < R := by linarith [hz.1]
    exact ⟨by simpa only [mem_ball_zero_iff] using hwsmall, hwpos, hwR⟩
  have hfin : (∫⁻ w in U, ENNReal.ofReal (‖F w‖ ^ 2) ∂volume) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set inter_subset_right) hL2
  have hbound := holomorphic_norm_sq_le_l2 F hU (hF.mono inter_subset_right) hfin z (‖z‖ / 2)
    (half_pos hr) hball
  apply Real.le_sqrt_of_sq_le
  calc
    (‖z‖ * ‖F z‖) ^ 2 = ‖z‖ ^ 2 * ‖F z‖ ^ 2 := by ring
    _ ≤ ‖z‖ ^ 2 * ((Real.pi * (‖z‖ / 2) ^ 2)⁻¹ * (T (2 * ‖z‖)).toReal) := by
      exact mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by
      field_simp
      <;> ring

private theorem littleO_inverse_of_norm_mul {q : ℕ} (F : ℂ → ComplexVector q)
    (h : Tendsto (fun z : ℂ => ‖z‖ * ‖F z‖) (𝓝[≠] 0) (𝓝 0)) :
    F =o[𝓝[≠] (0 : ℂ)] (fun z : ℂ => z⁻¹) := by
  apply Asymptotics.IsLittleO.of_norm_left
  apply Asymptotics.IsLittleO.of_norm_right
  apply (Asymptotics.isLittleO_iff_tendsto' ?_).2
  · simpa only [norm_inv, div_inv_eq_mul, mul_comm] using h
  · filter_upwards [self_mem_nhdsWithin] with z hz
    intro heq
    have hz0 : z = 0 := by simpa only [norm_eq_zero, inv_eq_zero] using heq
    exact (hz hz0).elim

/-- A finite area L² holomorphic map on a punctured disc has a holomorphic extension. -/
theorem exists_holomorphic_l2_extension {q : ℕ} (R : ℝ) (hR : 0 < R)
    (F : ℂ → ComplexVector q)
    (hF : DifferentiableOn ℂ F {z | 0 < ‖z‖ ∧ ‖z‖ < R})
    (hL2 : (∫⁻ z in {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < R},
      ENNReal.ofReal (‖F z‖ ^ 2) ∂volume) < ⊤) :
    ∃ G : ℂ → ComplexVector q, DifferentiableOn ℂ G (ball 0 R) ∧
      ∀ z, 0 < ‖z‖ → ‖z‖ < R → G z = F z := by
  classical
  have hsmall := littleO_inverse_of_norm_mul F (holomorphic_l2_norm_mul_tendsto R hR F hF hL2)
  have hconst : (fun _ : ℂ => F 0) =o[𝓝[≠] (0 : ℂ)] (fun z : ℂ => z⁻¹) := by
    apply littleO_inverse_of_norm_mul
    simpa only [norm_zero, zero_mul] using
      ((continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).mul_const ‖F 0‖
  have ho : (fun z : ℂ => F z - F 0) =o[𝓝[≠] 0] (fun z : ℂ => (z - 0)⁻¹) := by
    simpa only [sub_zero] using hsmall.sub hconst
  have hd : DifferentiableOn ℂ F (ball (0 : ℂ) R \ {0}) := by
    apply hF.mono
    intro z hz
    exact ⟨norm_pos_iff.mpr hz.2, by simpa only [mem_ball_zero_iff] using hz.1⟩
  have hext := Complex.differentiableOn_update_limUnder_of_isLittleO (ball_mem_nhds (0 : ℂ) hR) hd ho
  refine ⟨Function.update F 0 (limUnder (𝓝[≠] (0 : ℂ)) F), hext, ?_⟩
  intro z hz _
  simp [Function.update_of_ne (norm_pos_iff.mp hz)]

end Yau.Proofs.D03Aux
