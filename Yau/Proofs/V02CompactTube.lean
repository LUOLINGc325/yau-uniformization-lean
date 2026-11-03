import Yau.Proofs.V03NativeMaps
import Mathlib.Topology.MetricSpace.Thickening

/-! A genuine compact parameter tube, including empty compact sets and
empty finite families. Only continuity at the zero section is needed. -/

open scoped Topology
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof

theorem compact_parameter_tube
    {E P Y : Type*} [PseudoMetricSpace E] [NormedAddCommGroup P] [TopologicalSpace Y]
    {K : Set E} (hK : IsCompact K) {O : Set Y} (hO : IsOpen O)
    {F : E × P → Y}
    (hF : ∀ u ∈ K, ContinuousAt F (u, 0))
    (hzero : ∀ u ∈ K, F (u, 0) ∈ O) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ K, ∀ τ ∈ closedBall (0 : P) r, F (u, τ) ∈ O := by
  let C : Set (E × P) := K ×ˢ {0}
  have hC : IsCompact C := hK.prod isCompact_singleton
  have hnear : C ⊆ interior (F ⁻¹' O) := by
    rintro ⟨u, τ⟩ ⟨hu, hτ⟩
    have he : τ = 0 := mem_singleton_iff.mp hτ
    subst τ
    exact mem_interior_iff_mem_nhds.mpr
      ((hF u hu).preimage_mem_nhds (hO.mem_nhds (hzero u hu)))
  obtain ⟨δ, hδ, hsub⟩ := hC.exists_thickening_subset_open isOpen_interior hnear
  refine ⟨δ / 2, half_pos hδ, fun u hu τ hτ => ?_⟩
  have hτδ : ‖τ‖ < δ := (by simpa using mem_closedBall.mp hτ : ‖τ‖ ≤ δ / 2).trans_lt
    (half_lt_self hδ)
  have hmem : (u, τ) ∈ thickening δ C := mem_thickening_iff.mpr
    ⟨(u, 0), ⟨hu, mem_singleton _⟩, by simpa [Prod.dist_eq] using hτδ⟩
  exact (interior_subset : interior (F ⁻¹' O) ⊆ F ⁻¹' O) (hsub hmem)

theorem finite_compact_parameter_tube
    {ι E P Y : Type*} [Fintype ι] [PseudoMetricSpace E]
    [NormedAddCommGroup P] [TopologicalSpace Y]
    {K : ι → Set E} (hK : ∀ i, IsCompact (K i))
    {O : ι → Set Y} (hO : ∀ i, IsOpen (O i))
    {F : ι → E × P → Y}
    (hF : ∀ i u, u ∈ K i → ContinuousAt (F i) (u, 0))
    (hzero : ∀ i u, u ∈ K i → F i (u, 0) ∈ O i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i u, u ∈ K i →
      ∀ τ ∈ closedBall (0 : P) r, F i (u, τ) ∈ O i := by
  classical
  choose r hr hmap using fun i => compact_parameter_tube (hK i) (hO i) (hF i) (hzero i)
  let A : ℝ := 1 + ∑ i, (r i)⁻¹
  have hsum : 0 ≤ ∑ i, (r i)⁻¹ := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hr i).le)
  have hA : 0 < A := by dsimp [A]; linarith
  have hsmall (i : ι) : A⁻¹ ≤ r i := by
    rw [← one_div]
    apply (div_le_iff₀ hA).mpr
    have hi : (r i)⁻¹ ≤ A := by
      have hh := Finset.single_le_sum (fun i _ => (inv_pos.mpr (hr i)).le) (Finset.mem_univ i)
      dsimp [A]
      linarith
    calc
      1 = r i * (r i)⁻¹ := (mul_inv_cancel₀ (hr i).ne').symm
      _ ≤ r i * A := mul_le_mul_of_nonneg_left hi (hr i).le
  exact ⟨A⁻¹, inv_pos.mpr hA, fun i u hu τ hτ =>
    hmap i u hu τ ((closedBall_subset_closedBall (hsmall i)) hτ)⟩

end Yau.Blueprint.V02Proof
