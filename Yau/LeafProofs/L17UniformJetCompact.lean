import Yau.LeafProofs.L17UniformJetOperations

/-! Compact buffers give simultaneous uniform bounds for every finite smooth jet. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

theorem compact_buffer_uniformJetBounds
    {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧
      ∀ k, UniformJetBounds k (fun _ : ι => f) (fun _ => V) := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  refine ⟨V, hVo, hKV, hVU, ?_⟩
  intro k
  apply UniformJetBounds.of_orderBounds
  intro j hj
  have hc := (ContinuousOn.continuousOn_iteratedFDeriv hf hU
    (by simp : (j : ℕ∞ω) ≤ ∞)).mono hVU
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hc
  exact ⟨C, fun _ x hx => hC x (subset_closure hx)⟩

end Yau.LeafProofs.L17Aux
