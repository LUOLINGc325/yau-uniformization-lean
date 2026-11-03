import Yau.Proofs.F04ChartContinuity

open Filter Set
open scoped Topology
noncomputable section
namespace Yau.F04Proof

/-- The actual compact finite-cover argument upgrades continuous
 antitone convergence to zero to the uniform upper bound needed for
 supercaloric tails. Only relative continuity on the compact set is used. -/
theorem compact_antitone_uniform_upper_zero
    {α : Type*} [TopologicalSpace α] {K : Set α} (hK : IsCompact K)
    (v : ℕ → α → ℝ) (hv : ∀ j, ContinuousOn (v j) K)
    (hAnti : ∀ x ∈ K, Antitone (fun j => v j x))
    (hPoint : ∀ x ∈ K, Tendsto (fun j => v j x) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ K, v j x ≤ ε := by
  intro ε hε
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : ℕ → Set K := fun j => {x | v j x.val < ε}
  have hU (j : ℕ) : IsOpen (U j) := isOpen_lt (hv j).domRestrict continuous_const
  have hCover : (univ : Set K) ⊆ ⋃ j : ℕ, U j := by
    intro x _hx
    obtain ⟨J,hJ⟩ := eventually_atTop.mp ((hPoint x.val x.property).eventually (gt_mem_nhds hε))
    exact mem_iUnion.mpr ⟨J,hJ J le_rfl⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU hCover
  refine ⟨s.sup id,?_⟩
  intro j hj x hx
  obtain ⟨i,hi,hix⟩ := mem_iUnion₂.mp (hs (mem_univ (⟨x,hx⟩ : K)))
  have hij : i ≤ j := (Finset.le_sup (f := id) hi).trans hj
  exact ((hAnti x hx hij).trans_lt hix).le

end Yau.F04Proof
