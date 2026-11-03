import Yau.Proofs.F04AuxiliaryBuffer

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace Yau.F04Proof

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem linear_growth_slice_bound {S K : ℝ} {u : α × ℝ → ℝ}
    (_hK : 0 ≤ K) (t : ℝ) (_ht : t ∈ Ioo 0 S)
    (hbound : ∀ᵐ x ∂μ, |u (x, t)| ≤ K * t) :
    0 ≤ (∫ x, |u (x, t)| ^ 2 ∂μ) ∧
      (∫ x, |u (x, t)| ^ 2 ∂μ) ≤ (K * t) ^ 2 * μ.real univ := by
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  have hn : ∀ᵐ x ∂μ, ‖|u (x, t)| ^ 2‖ ≤ (K * t) ^ 2 := by
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hn)

theorem linear_growth_initial_trace {S K : ℝ} {u : α × ℝ → ℝ}
    (hS : 0 < S) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioo 0 S, ∀ᵐ x ∂μ, |u (x, t)| ≤ K * t) :
    Tendsto (fun t => ∫ x, |u (x, t)| ^ 2 ∂μ) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun t => integral_nonneg (fun _ => sq_nonneg _)))
    (eventually_of_mem (Ioo_mem_nhdsGT hS) (fun t ht =>
      (linear_growth_slice_bound hK t ht (hbound t ht)).2))
  have hh : Tendsto (fun t : ℝ => (K * t) ^ 2 * μ.real univ) (𝓝 0) (𝓝 0) := by
    have hKt : Tendsto (fun t : ℝ => K * t) (𝓝 0) (𝓝 0) := by
      convert (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).const_mul K using 1 <;>
        simp only [id_eq, mul_zero]
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] using
      (hKt.pow 2).mul_const (μ.real univ)
  exact hh.mono_left nhdsWithin_le_nhds

end Yau.F04Proof
