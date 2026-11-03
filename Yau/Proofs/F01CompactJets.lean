import spec.CHAIN.CONTRACTS

/-! Compact-family budgets for all actual derivative orders. The sequence of
bounds is chosen before every point of the compact parameter family. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_all_derivative_budgets {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ k x, x ∈ K → ‖iteratedFDeriv ℝ k f x‖ ≤ C k := by
  have hex : ∀ k : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k f) K :=
      ((hf.continuousOn_iteratedFDerivWithin
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) hU.uniqueDiffOn).mono hKU).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen k hU (hKU hx)).symm)
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨max 1 B + 1, by positivity, ?_⟩
    intro x hx
    exact (hB x hx).trans (by linarith [le_max_right (1 : ℝ) B])
  choose C hC hbound using hex
  exact ⟨C, hC, fun k x hx => hbound k x hx⟩

end Yau.NodeProofs.F01Aux
