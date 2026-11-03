import Yau.Proofs.F04ChartCoefficients

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.LeafProofs.L18Aux

/-- Every actual interior manifold point has three genuine precompact
 coordinate buffers inside the same physical domain. No finite atlas,
 boundary regularity or metric completeness is used. -/
theorem exists_interior_chart_buffers
    {n : ℕ} {M : ComplexManifold n} {Ω : Set M.Carrier} (hΩ : IsOpen Ω)
    (x : M.Carrier) (hx : x ∈ Ω) :
    ∃ O V W : Set (Space n), IsOpen O ∧ IsCompact (closure O) ∧
      closure O ⊆ chartTarget x ∧ chartInv x '' O ⊆ Ω ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ V ∧ chartPt x x ∈ W := by
  let Q : Set (Space n) := chartTarget x ∩ chartInv x ⁻¹' Ω
  have hQ : IsOpen Q := (continuousOn_extChartAt_symm (I := ComplexModel n) x).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel n) x) hΩ
  have hxQ : ({chartPt x x} : Set (Space n)) ⊆ Q := by
    intro z hz
    rw [mem_singleton_iff.mp hz]
    refine ⟨mem_extChartAt_target x,?_⟩
    change chartInv x (chartPt x x) ∈ Ω
    rw [Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact hx
  obtain ⟨O,hO,hxO,hOQ,hOC⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hQ hxQ
  obtain ⟨V,hV,hxV,hVO,hVC⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hO hxO
  obtain ⟨W,hW,hxW,hWV,hWC⟩ := exists_open_between_and_isCompact_closure isCompact_singleton hV hxV
  refine ⟨O,V,W,hO,hOC,?_,?_,hV,hVC,hVO,hW,hWC,hWV,hxW (mem_singleton _)⟩
  · exact fun z hz => (hOQ hz).1
  · rintro y ⟨z,hz,rfl⟩
    exact (hOQ (subset_closure hz)).2

end Yau.F04Proof
