import Yau.Proofs.F04FiniteMass

open Filter
open scoped Topology

noncomputable section

namespace Yau.F04Proof

/-- Uniform operator bounds pass strong convergence through a varying input. -/
theorem uniformly_bounded_operators_apply_tendsto
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} (T : ι → E →L[ℝ] F) (C : ℝ) (hT : ∀ i, ‖T i‖ ≤ C)
    (x : ι → E) (x₀ : E) (y : F) (hx : Tendsto x l (𝓝 x₀))
    (hy : Tendsto (fun i => T i x₀) l (𝓝 y)) :
    Tendsto (fun i => T i (x i)) l (𝓝 y) := by
  have hd : Tendsto (fun i => T i (x i - x₀)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => (T i).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, mul_zero] using
      ((hx.sub (tendsto_const_nhds : Tendsto (fun _ : ι => x₀) l (𝓝 x₀))).norm.const_mul C)
  simpa only [map_sub, sub_add_cancel, zero_add] using hd.add hy

end Yau.F04Proof
