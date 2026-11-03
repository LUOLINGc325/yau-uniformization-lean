import Yau.Proofs.F03CaloricNorms
import Yau.LeafProofs.L16L2Products

/-! Actual bounded pointwise convergence gives strong L² convergence on finite cylinders. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem bounded_pointwise_integral_sq_tendsto {d : ℕ} (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (f : ℕ → Point d → ℝ) (v : Point d → ℝ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hv : AEStronglyMeasurable v μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ j, ∀ᵐ p ∂μ, ‖f j p‖ ≤ B)
    (hPoint : ∀ᵐ p ∂μ,Tendsto (fun j => f j p) atTop (𝓝 (v p))) :
    MemLp v 2 μ ∧ Tendsto (fun j => ∫ p,‖f j p-v p‖^2 ∂μ) atTop (𝓝 0) := by
  have hVBound : ∀ᵐ p ∂μ,‖v p‖ ≤ B := by
    filter_upwards [hPoint,ae_all_iff.mpr hBound] with p hp hb
    exact le_of_tendsto hp.norm (Eventually.of_forall hb)
  refine ⟨MemLp.of_bound hv B hVBound,?_⟩
  have hInt : Tendsto (fun j => ∫ p,‖f j p-v p‖^2 ∂μ) atTop (𝓝 (∫ _ : Point d,(0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Point d => (2*B)^2)
    · intro j
      convert (((hf j).aestronglyMeasurable.sub hv).norm.pow 2) using 1
    · exact integrable_const _
    · intro j
      filter_upwards [hBound j,hVBound] with p hp hvp
      have hn : ‖f j p-v p‖ ≤ 2*B := by
        calc
          _ ≤ ‖f j p‖+‖v p‖ := norm_sub_le _ _
          _ ≤ 2*B := by linarith
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hn
    · filter_upwards [hPoint] with p hp
      have h := ((hp.sub (tendsto_const_nhds (x := v p))).norm).pow 2
      simpa only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] using h
  simpa only [integral_zero] using hInt

theorem bounded_pointwise_toLp_tendsto {d : ℕ} (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (f : ℕ → Point d → ℝ) (v : Point d → ℝ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hv : MemLp v 2 μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ j, ∀ᵐ p ∂μ, ‖f j p‖ ≤ B)
    (hPoint : ∀ᵐ p ∂μ,Tendsto (fun j => f j p) atTop (𝓝 (v p))) :
    Tendsto (fun j => (hf j).toLp (f j)) atTop (𝓝 (hv.toLp v)) :=
  LeafProofs.L16Aux.tendsto_toLp_of_integral_sq_sub hf hv
    (bounded_pointwise_integral_sq_tendsto μ f v hf hv.aestronglyMeasurable B hB hBound hPoint).2

end Yau.Proofs.F03Aux
