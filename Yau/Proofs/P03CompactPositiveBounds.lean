import Yau.Geometry.Calculus

open scoped Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

/-- Positive local constants for a monotone estimate give one positive
constant on a compact set. Empty compact sets need no separate hypothesis. -/
theorem exists_compact_positive_bound {A : Type*} [TopologicalSpace A]
    (P : ℝ → A → Prop) (hmono : ∀ s t, s ≤ t → ∀ x, P t x → P s x)
    (hlocal : ∀ x : A, ∃ t : ℝ, 0 < t ∧ ∃ U : Set A, U ∈ 𝓝 x ∧ ∀ y ∈ U, P t y)
    {K : Set A} (hK : IsCompact K) :
    ∃ t : ℝ, 0 < t ∧ ∀ x ∈ K, P t x := by
  classical
  choose t ht U hU hP using hlocal
  obtain ⟨s, hsK, hcover⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  let D : ℝ := 1 + ∑ x ∈ s, (t x)⁻¹
  have hsum : 0 ≤ ∑ x ∈ s, (t x)⁻¹ :=
    Finset.sum_nonneg (fun x _ => inv_nonneg.mpr (ht x).le)
  have hD : 0 < D := by dsimp only [D]; linarith
  refine ⟨1 / D, one_div_pos.mpr hD, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
  have hinv : (t y)⁻¹ ≤ ∑ z ∈ s, (t z)⁻¹ :=
    Finset.single_le_sum (fun z _ => inv_nonneg.mpr (ht z).le) hys
  have hprod : 1 ≤ t y * (∑ z ∈ s, (t z)⁻¹) := by
    have hh := mul_le_mul_of_nonneg_left hinv (ht y).le
    rwa [mul_inv_cancel₀ (ht y).ne'] at hh
  have hle : 1 / D ≤ t y := by
    apply (div_le_iff₀ hD).mpr
    dsimp only [D]
    nlinarith [ht y]
  exact hmono _ _ hle x (hP y x hxy)

end Yau.NodeProofs.P03Aux
