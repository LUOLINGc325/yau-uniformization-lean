import Yau.Proofs.F01CompactUniformSubsequence

/-! One subsequence works simultaneously for a countable family of
compact domains and finite-dimensional jet targets. The targets may vary
with the derivative order. -/
noncomputable section
open Set Filter
open scoped BoundedContinuousFunction
namespace Yau.NodeProofs.F01Aux
variable {A F : ℕ → Type*}
  [∀ k, TopologicalSpace (A k)] [∀ k, CompactSpace (A k)]
  [∀ k, NormedAddCommGroup (F k)] [∀ k, ProperSpace (F k)]

theorem countable_uniform_subsequence
    (u : ℕ → ∀ k, A k →ᵇ F k)
    (hEqui : ∀ k, Equicontinuous (fun m x => u m k x))
    (B : ℕ → ℝ) (hB : ∀ k m x, ‖u m k x‖ ≤ B k) :
    ∃ v : ∀ k, A k →ᵇ F k, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ k, TendstoUniformly (fun m x => u (σ m) k x) (fun x => v k x) atTop := by
  let K : ∀ k, Set (A k →ᵇ F k) := fun k => closure (range (fun m => u m k))
  have hK (k : ℕ) : IsCompact (K k) :=
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
