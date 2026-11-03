import Yau.Proofs.F05SupportedPoint
import Yau.Proofs.F05CanonicalRealization

/-! A second literal reconstruction uses the genuine partition as the inner
cutoff. It has the same physical values as the canonical realization. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_outer_partition_product {O : Set M.Carrier} {A : AtlasData M}
    {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (j : Fin A.count) (β : M.Carrier → ℝ)
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A j z) = 1)
    (x : M.Carrier) : β x*χ j x = χ j x := by
  by_cases hx : χ j x = 0
  · rw [hx,mul_zero]
  obtain ⟨z,hz,heq⟩ := hχ.2.2.1 j (subset_tsupport (χ j) hx)
  have hβ : β x = 1 := by
    rw [← heq]
    exact hOne z (Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1/2) hz)
  rw [hβ,one_mul]

def F05CutoffReconstruction (A : AtlasData M) (χ β : Fin A.count → M.Carrier → ℝ)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    (x : M.Carrier) (t : ℝ) : ℝ :=
  ∑ j,F05ManifoldPatch A j (β j)
    (F05LocalJetExtension A j (F05ModelPartition A χ j) (u.val j).val) x t

theorem F05_cutoff_reconstruction_term {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (j : Fin A.count) (β : M.Carrier → ℝ)
    (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A j z) = 1)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    {x : M.Carrier} (hx : x ∈ closure O) (t : ℝ) :
    F05ManifoldPatch A j β (F05LocalJetExtension A j (F05ModelPartition A χ j) (u.val j).val) x t =
      χ j x*F05LocalJetExtension A j (F05InnerPlateau n) (u.val j).val (F05Coord A j x,t) := by
  have hProduct := F05_outer_partition_product hχ j β hOne x
  by_cases hβ : β x = 0
  · have hχx : χ j x = 0 := by simpa only [hβ,zero_mul] using hProduct.symm
    simp only [F05ManifoldPatch,hβ,hχx,zero_mul]
  have hCoord := F05_supported_coord hA j hSupport hx hβ
  have hz3 := F05D_mem_ball hCoord.1
  have hExtension := F05LocalJetExtension_value_on_model A j (F05ModelPartition A χ j)
    (u.val j).val (p := (F05Coord A j x,t)) (F05D_subset_model_closure A j hCoord.1)
  have hPartition : F05ModelPartition A χ j (F05Coord A j x) = χ j x := by
    rw [F05ModelPartition_eq hA hχ j hz3,hCoord.2.2]
  unfold F05ManifoldPatch
  rw [hExtension]
  unfold F05CutoffJetValue
  rw [hPartition,← mul_assoc,hProduct]
  by_cases hχx : χ j x = 0
  · rw [hχx,zero_mul,zero_mul]
  have hNonzero : χ j (lift A j (F05Coord A j x)) ≠ 0 := by rwa [hCoord.2.2]
  have hn := F05_partition_pull_nonzero_norm hA hχ j hz3 hNonzero
  rw [F05InnerExtension_value A j α T (u.val j).val (F05Coord A j x) hCoord.1 hn t]

theorem F05CutoffReconstruction_eq {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (β : Fin A.count → M.Carrier → ℝ)
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    (hOne : ∀ j z, z ∈ Metric.closedBall (0 : Space n) (1/2) → β j (lift A j z) = 1)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05CompatibleJetGraph A α hT)
    {x : M.Carrier} (hx : x ∈ closure O) (t : ℝ) :
    F05CutoffReconstruction A χ β α hT u x t = F05CanonicalJetFunction A χ α hT u x t := by
  unfold F05CutoffReconstruction F05CanonicalJetFunction
  exact Finset.sum_congr rfl (fun j _ =>
    F05_cutoff_reconstruction_term hA hχ j (β j) (hSupport j) (hOne j) α hT u hx t)

end Yau.Proofs.F05Aux
