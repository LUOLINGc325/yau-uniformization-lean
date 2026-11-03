import Yau.LeafProofs.L03
import Mathlib.Topology.MetricSpace.Thickening

open MeasureTheory Filter
open scoped Topology Convolution Pointwise

noncomputable section

namespace Yau.LeafProofs.L03

/-- Choose all mollifier scales small enough that every convolution of
a raw field supported in a fixed compact set stays in its chosen open
buffer. This is uniform over the raw input and includes dimension zero. -/
theorem exists_mollifier_scales_in_compact_buffer {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (ρ : E → ℝ) (hcρ : HasCompactSupport ρ)
    {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 < ε m) ∧ (∀ m, ε m ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ f : E → ℝ, tsupport f ⊆ K → ∀ m,
        tsupport (rescaledFriedrichsMollifier ρ (ε m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) ⊆ O := by
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨R, hR, hρR⟩ := hcρ.isBounded.exists_pos_norm_le
  let η : ℝ := min 1 (δ / (R + 1))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hδ (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηR : η * R ≤ δ := by
    have h : η * (R + 1) ≤ δ := (le_div_iff₀ (show 0 < R + 1 by linarith)).mp
      (min_le_right 1 (δ / (R + 1)))
    nlinarith
  let ε := fun m : ℕ => η / ((m : ℝ) + 1)
  have hε (m : ℕ) : 0 < ε m := div_pos hη (by positivity)
  have hεη (m : ℕ) : ε m ≤ η := by
    apply (div_le_iff₀ (show 0 < (m : ℝ) + 1 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  refine ⟨ε, hε, fun m => (hεη m).trans hη1, ?_, ?_⟩
  · exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  · intro f hf m
    let S : Set E := K + Metric.closedBall (0 : E) δ
    have hcS : IsCompact S := hK.add (isCompact_closedBall 0 δ)
    have hS : S ⊆ O := by
      rintro z ⟨k, hk, w, hw, rfl⟩
      apply hδO
      apply Metric.mem_cthickening_of_dist_le (k + w) k δ K hk
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
    have hρm : Function.support (rescaledFriedrichsMollifier ρ (ε m)) ⊆ Metric.closedBall (0 : E) δ := by
      intro z hz
      have hρz : ρ ((ε m)⁻¹ • z) ≠ 0 := by
        intro hzero
        exact hz (by simp only [rescaledFriedrichsMollifier, hzero, mul_zero])
      apply Metric.mem_closedBall.mpr
      rw [dist_zero_right]
      calc
        ‖z‖ = ‖ε m • ((ε m)⁻¹ • z)‖ := by
          rw [smul_smul, mul_inv_cancel₀ (hε m).ne', one_smul]
        _ = ε m * ‖(ε m)⁻¹ • z‖ := by rw [norm_smul, Real.norm_of_nonneg (hε m).le]
        _ ≤ ε m * R := mul_le_mul_of_nonneg_left (hρR _ (subset_closure hρz)) (hε m).le
        _ ≤ η * R := mul_le_mul_of_nonneg_right (hεη m) hR.le
        _ ≤ δ := hηR
    have hs : Function.support
        (rescaledFriedrichsMollifier ρ (ε m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) ⊆ S :=
      (MeasureTheory.support_convolution_subset_swap (f := rescaledFriedrichsMollifier ρ (ε m))
        (g := f) (μ := ν) (ContinuousLinearMap.lsmul ℝ ℝ)).trans
        (Set.add_subset_add (subset_closure.trans hf) hρm)
    exact (closure_minimal hs hcS.isClosed).trans hS

end Yau.LeafProofs.L03
