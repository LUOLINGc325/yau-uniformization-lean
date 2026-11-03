import Yau.Proofs.C07ChartBallMaps

open scoped Manifold Topology unitInterval

noncomputable section

namespace Yau.Proofs.C07ConnectedExhaustionAux

open Yau Set C07Aux D04AtlasGlueAux

variable {n : ℕ} {M : ComplexManifold n}

/-- Finitely many chart cores, joined to a fixed point by actual paths,
give a compact connected enlargement of an arbitrary compact set. -/
theorem exists_compact_preconnected_superset (o : M.Carrier) {K : Set M.Carrier}
    (hK : IsCompact K) :
    ∃ L : Set M.Carrier, IsCompact L ∧ IsPreconnected L ∧ o ∈ L ∧ K ⊆ L := by
  classical
  letI : LocallyPathConnectedSpace M.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (ComplexVector n) M.Carrier
  letI : PathConnectedSpace M.Carrier := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨B, hB⟩ := exists_countable_chartBalls M
  obtain ⟨S, hS⟩ := finite_chartBall_cover B hB (hK.union isCompact_singleton)
  let p : ∀ i : S, Path o (B i).center :=
    fun i => PathConnectedSpace.somePath o (B i).center
  let F : S → Set M.Carrier := fun i => closure (B i).inner ∪ range (p i)
  have hFc : ∀ i : S, IsCompact (F i) := fun i =>
    ((B i).isCompact_core.of_isClosed_subset isClosed_closure (B i).closure_inner_subset_core).union
      (isCompact_range (p i).continuous)
  have hFconn : ∀ i : S, IsPreconnected (F i) := by
    intro i
    exact ((chartBall_inner_preconnected (B i)).closure).union (B i).center
      (subset_closure (B i).center_mem_inner) (p i).target_mem_range
      (isPreconnected_range (p i).continuous)
  have hoF : ∀ i : S, o ∈ F i := fun i => Or.inr (p i).source_mem_range
  have hSn : Nonempty S := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hS (Or.inr (mem_singleton o)))
    obtain ⟨hiS, _⟩ := mem_iUnion.mp hi
    exact ⟨⟨i, hiS⟩⟩
  letI := hSn
  refine ⟨⋃ i : S, F i, isCompact_iUnion hFc,
    isPreconnected_iUnion ⟨o, mem_iInter.mpr hoF⟩ hFconn,
    mem_iUnion.mpr ⟨Classical.choice hSn, hoF _⟩, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hS (Or.inl hx))
  obtain ⟨hiS, hxi⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨⟨i, hiS⟩, Or.inl (subset_closure hxi)⟩

/-- A compact set lies in a connected open neighborhood of the base point
with compact closure. -/
theorem exists_precompact_preconnected_open (o : M.Carrier) {K : Set M.Carrier}
    (hK : IsCompact K) :
    ∃ V : Set M.Carrier, IsOpen V ∧ IsPreconnected V ∧ IsCompact (closure V) ∧
      o ∈ V ∧ K ⊆ V := by
  letI : LocallyConnectedSpace M.Carrier :=
    ChartedSpace.locallyConnectedSpace (ComplexVector n) M.Carrier
  letI : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace (ComplexVector n) M.Carrier
  obtain ⟨L, hLc, hLconn, hoL, hKL⟩ := exists_compact_preconnected_superset o hK
  obtain ⟨U, hUo, hLU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hLc
  have hLV : L ⊆ connectedComponentIn U o :=
    hLconn.subset_connectedComponentIn hoL hLU
  exact ⟨connectedComponentIn U o, hUo.connectedComponentIn,
    isPreconnected_connectedComponentIn,
    hUc.of_isClosed_subset isClosed_closure (closure_mono (connectedComponentIn_subset U o)),
    hLV hoL, hKL.trans hLV⟩

end Yau.Proofs.C07ConnectedExhaustionAux
