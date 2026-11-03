import Yau.Proofs.F01CompactJets
import Yau.Proofs.F01FiniteBudgets

/-! Uniform derivative bounds on finitely many actual compact coordinate
buffers. Bounds are selected before the chart index and the point. -/
open Set
open scoped ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_compact_all_derivative_budgets (s : Finset ι)
    (U K : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i) (f : ι → E → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i)) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ i ∈ s, ∀ k x, x ∈ K i →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C k := by
  classical
  have hi := fun i => compact_all_derivative_budgets (hU i) (hK i) (hKU i) (hf i)
  choose B hB hbound using hi
  obtain ⟨C, hC, hBC, _⟩ := exists_finite_uniform_budgets s B (fun _ => 0)
  exact ⟨C, hC, fun i his k x hx => (hbound i k x hx).trans (hBC i his k)⟩

theorem finite_compact_fderiv_budget (s : Finset ι)
    (U K : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ U i) (f : ι → E → F) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (U i)) :
    ∃ M : ℝ, 0 < M ∧ ∀ i ∈ s, ∀ x ∈ K i, ‖fderiv ℝ (f i) x‖ ≤ M := by
  obtain ⟨C, hC, hb⟩ := finite_compact_all_derivative_budgets s U K hU hK hKU f hf
  refine ⟨C 1, hC 1, ?_⟩
  intro i hi x hx
  simpa only [norm_iteratedFDeriv_one] using hb i hi 1 x hx

end Yau.NodeProofs.F01Aux
