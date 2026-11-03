import Yau.Blueprint.Nodes
import Mathlib.Topology.Separation.Regular

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {D : Type*} [TopologicalSpace D] [T2Space D] [RegularSpace D] [LocallyCompactSpace D]

/-- A neighborhood of the ENTIRE compact equality set, with compact
closure inside the original physical/full-rank open domain. -/
theorem exists_open_precompact_between (K U : Set D) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ O : Set D, IsOpen O ∧ K ⊆ O ∧ IsCompact (closure O) ∧ closure O ⊆ U := by
  obtain ⟨V,hV,hKV,hVC⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨O,hO,hKO,hSub⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hV).mem_nhdsSet.mpr (fun x hx => ⟨hKU hx,hKV hx⟩))
  refine ⟨O,hO,hKO,hVC.of_isClosed_subset isClosed_closure ?_,fun x hx => (hSub hx).1⟩
  intro x hx
  exact subset_closure (hSub hx).2

/-- The compact source is chosen once BEFORE the regularization scale. -/
theorem exists_compact_source (K U : Set D) (hK : IsCompact K) (hNE : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ S : Set D, IsCompact S ∧ S.Nonempty ∧ K ⊆ interior S ∧ S ⊆ U := by
  obtain ⟨O,hO,hKO,hC,hSub⟩ := exists_open_precompact_between K U hK hU hKU
  have hOI : O ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds hx) subset_closure)
  refine ⟨closure O,hC,?_,hKO.trans hOI,hSub⟩
  obtain ⟨x,hx⟩ := hNE
  exact ⟨x,subset_closure (hKO hx)⟩

/-- A genuine lower semicontinuous support gap has a uniform strictly
positive boundary minimum; an empty frontier is handled directly. -/
theorem exists_positive_frontier_gap (O : Set D) (hO : IsOpen O) (hOC : IsCompact (closure O))
    (F : D → ℝ) (hF : LowerSemicontinuousOn F (closure O))
    (h0 : ∀ x ∈ closure O, 0 ≤ F x) (hZero : ∀ x ∈ closure O, F x = 0 → x ∈ O) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ frontier O, γ ≤ F x := by
  by_cases hNE : (frontier O).Nonempty
  · have hFC : IsCompact (frontier O) :=
      hOC.of_isClosed_subset isClosed_frontier frontier_subset_closure
    obtain ⟨x,hx,hMin⟩ := LowerSemicontinuousOn.exists_isMinOn hNE hFC
      (hF.mono frontier_subset_closure)
    have hNotZero : F x ≠ 0 := by
      intro hz
      have hxO := hZero x (frontier_subset_closure hx) hz
      have hxN : x ∉ interior O := hx.2
      rw [hO.interior_eq] at hxN
      exact hxN hxO
    exact ⟨F x,lt_of_le_of_ne (h0 x (frontier_subset_closure hx)) hNotZero.symm,
      fun y hy => hMin hy⟩
  · exact ⟨1,by norm_num,fun x hx => False.elim (hNE ⟨x,hx⟩)⟩

end Yau.NodeProofs.E02Aux
