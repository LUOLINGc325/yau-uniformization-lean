import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Compact bounds for actual iterated Fréchet derivatives. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02FlowProof

theorem compact_iteratedFDeriv_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖iteratedFDeriv ℝ m f p‖ ≤ C := by
  have hc := (ContinuousOn.continuousOn_iteratedFDeriv hf hO
    (by simp : (m : ℕ∞ω) ≤ ∞)).mono hKO
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun p hp =>
    (hC _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)⟩

theorem compact_iteratedFDeriv_finite_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O K : Set E} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ≤ q, ∀ p ∈ K, ‖iteratedFDeriv ℝ m f p‖ ≤ C := by
  classical
  choose C hC hbound using fun m : Fin (q + 1) =>
    compact_iteratedFDeriv_bound hO hK hKO hf m.val
  refine ⟨∑ m, C m, Finset.sum_nonneg (fun m _ => hC m), fun m hm p hp => ?_⟩
  exact (hbound ⟨m, Nat.lt_succ_of_le hm⟩ p hp).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ _))

end Yau.Blueprint.V02FlowProof
