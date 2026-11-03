import Yau.Proofs.F01CompactUniformSubsequence

/-! A common uniform subsequence for any countable index of compact
chart domains and finite-dimensional jet targets, including chart/order pairs. -/
noncomputable section
open Set Filter
open scoped BoundedContinuousFunction
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Countable ι] {A F : ι → Type*}
  [∀ k, TopologicalSpace (A k)] [∀ k, CompactSpace (A k)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, ProperSpace (F k)]

theorem indexed_uniform_subsequence
    (u : ℕ → ∀ k, A k →ᵇ F k)
    (hEqui : ∀ k, Equicontinuous (fun m x => u m k x))
    (B : ι → ℝ) (hB : ∀ k m x, ‖u m k x‖ ≤ B k) :
    ∃ v : ∀ k, A k →ᵇ F k, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ k, TendstoUniformly (fun m x => u (σ m) k x) (fun x => v k x) atTop := by
  let K : ∀ k, Set (A k →ᵇ F k) := fun k => closure (range (fun m => u m k))
  have hK (k : ι) : IsCompact (K k) :=
    compact_uniform_family_closure (fun m => u m k) (hEqui k) (hB k)
  have hprod : IsCompact {v : ∀ k, A k →ᵇ F k | ∀ k, v k ∈ K k} :=
    isCompact_pi_infinite hK
  obtain ⟨v, hv, σ, hσ, hconv⟩ := hprod.tendsto_subseq
    (fun m k => subset_closure (mem_range_self m))
  refine ⟨v, σ, hσ, ?_⟩
  intro k
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
  have hcoordinate := (continuous_apply k).continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def] using hcoordinate

end Yau.NodeProofs.F01Aux
