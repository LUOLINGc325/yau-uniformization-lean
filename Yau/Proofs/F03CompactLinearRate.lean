import Yau.Proofs.F03EllipticCoefficientBounds

/-! Actual local linear rates give one rate before every point of a compact set. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux

theorem compact_linear_rate_of_local {E : Type*} [TopologicalSpace E]
    (K : Set E) (hK : IsCompact K) (F : ℝ → E → ℝ)
    (hLocal : ∀ x ∈ K,∃ U : Set E,IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ y ∈ K,y ∈ U → F t y ≤ C*t) :
    ∃ C : ℝ,0 < C ∧ ∀ t,0 < t → ∀ y ∈ K,F t y ≤ C*t := by
  classical
  choose U hU hx C hC hRate using (fun x : K => hLocal x.val x.property)
  have hCover : K ⊆ ⋃ x : K,U x := fun y hy => mem_iUnion.mpr ⟨⟨y,hy⟩,hx ⟨y,hy⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU hCover
  let A := 1+∑ i ∈ s,C i
  have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (hC i).le))
  refine ⟨A,hA,fun t ht y hy => ?_⟩
  obtain ⟨i,hi,hyU⟩ := mem_iUnion₂.mp (hs hy)
  have hCi : C i ≤ ∑ j ∈ s,C j := Finset.single_le_sum (fun j _ => (hC j).le) hi
  have hCiA : C i ≤ A := hCi.trans (by dsimp [A];linarith)
  exact (hRate i t ht y hy hyU).trans (mul_le_mul_of_nonneg_right hCiA ht.le)

end Yau.Proofs.F03Aux
