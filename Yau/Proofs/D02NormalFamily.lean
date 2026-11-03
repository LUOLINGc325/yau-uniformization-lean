import Yau.Proofs.D02CotangentCompact

/-! Properly extracted normal limits in the topology of uniform convergence
on compact subsets. This is the Arzelà--Ascoli extraction used on Δ minus the
locally finite concentration set. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux

/-- One increasing extraction works on every compact subset of the domain.
The hypotheses are equicontinuity and genuine compact pointwise ranges. -/
theorem continuousFamily_subsequence_uniformOn_compacts
    {D Y : Type*} [TopologicalSpace D] [LocallyCompactSpace D] [SigmaCompactSpace D]
    [MetricSpace Y] [CompleteSpace Y] (fs : ℕ → C(D, Y))
    (heq : ∀ K : Set D, IsCompact K → EquicontinuousOn (fun j x => fs j x) K)
    (hpt : ∀ x : D, ∃ Q : Set Y, IsCompact Q ∧ ∀ j : ℕ, fs j x ∈ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : C(D, Y),
      ∀ K : Set D, IsCompact K → TendstoUniformlyOn (fun j x => fs (φ j) x) f atTop K := by
  classical
  let F : C(D, Y) → D → Y := fun f => f
  let S : Set C(D, Y) := Set.range fs
  letI : T2Space (UniformOnFun D Y {K : Set D | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion.mpr ⟨{x}, isCompact_singleton, Set.mem_singleton x⟩)
  have hclemb : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set D | IsCompact K} ∘ F) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hSeq : ∀ K : Set D, IsCompact K →
      EquicontinuousOn (F ∘ ((↑) : S → C(D, Y))) K := by
    intro K hK
    let idx : S → ℕ := fun f => Classical.choose f.2
    have hi (f : S) : fs (idx f) = f.1 := Classical.choose_spec f.2
    have hfun : (fun f : S => (fun x => fs (idx f) x)) = F ∘ ((↑) : S → C(D, Y)) := by
      funext f x
      exact congrArg (fun h : C(D, Y) => h x) (hi f)
    rw [← hfun]
    exact (heq K hK).comp idx
  have hPoint : ∀ K : Set D, IsCompact K → ∀ x ∈ K,
      ∃ Q : Set Y, IsCompact Q ∧ ∀ f ∈ S, F f x ∈ Q := by
    intro K _ x _
    obtain ⟨Q, hQ, hp⟩ := hpt x
    refine ⟨Q, hQ, ?_⟩
    rintro f ⟨j, rfl⟩
    exact hp j
  have hcompact : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ hK => hK) hclemb hSeq hPoint
  obtain ⟨f, _, φ, hφ, ht⟩ := hcompact.tendsto_subseq
    (fun j => subset_closure (Set.mem_range_self j))
  refine ⟨φ, hφ, f, ?_⟩
  simpa only [Function.comp_apply] using
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht)

end Yau.NodeProofs.D02Aux
