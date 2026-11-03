import Yau.Proofs.F04BochnerL2

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

/-- Genuine strong L2 convergence from pointwise convergence and a common
L2 majorant for the differences, for arbitrary countably generated filters. -/
theorem toLp_tendsto_of_dominated_differences
    {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) {L : Filter ι} [L.IsCountablyGenerated]
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 μ) (u : X → E) (hu : MemLp u 2 μ)
    (b : X → ℝ) (hb : MemLp b 2 μ)
    (hbound : ∀ᶠ i in L, ∀ᵐ x ∂μ, ‖f i x - u x‖ ≤ b x)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) L (𝓝 (u x))) :
    Tendsto (fun i => (hf i).toLp (f i)) L (𝓝 (hu.toLp u)) := by
  let G := fun i x => ‖f i x - u x‖ ^ 2
  have hG (i : ι) : AEStronglyMeasurable (G i) μ :=
    (((hf i).aestronglyMeasurable.sub hu.aestronglyMeasurable).norm).pow 2
  have hGb : ∀ᶠ i in L, ∀ᵐ x ∂μ, ‖G i x‖ ≤ b x ^ 2 := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) L (𝓝 (0 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    simpa only [G, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((hx.sub (tendsto_const_nhds : Tendsto (fun _ : ι => u x) L (𝓝 (u x)))).norm).pow 2)
  have hInt := tendsto_integral_filter_of_dominated_convergence (fun x => b x ^ 2)
    (Eventually.of_forall hG) hGb hb.integrable_sq hlim
  have hs : Tendsto (fun i => ‖(hf i).toLp (f i) - hu.toLp u‖ ^ 2) L (𝓝 (0 : ℝ)) := by
    simpa only [bochner_toLp_sub_norm_sq, G, integral_zero] using hInt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end Yau.F04Proof
