import Yau.Proofs.F05Partition

/-! Genuine smooth manifold cutoffs for the outer parametrix product. Their
supports remain inside the region where the extended coefficients are exact. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_outer_manifold_cutoff {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) :
    ∃ β : M.Carrier → ℝ, SmoothFn β ∧ (∀ x, 0 ≤ β x ∧ β x ≤ 1) ∧
      tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4) ∧
      ∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A i z) = 1 := by
  classical
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := Yau.LeafProofs.L12Aux.manifold_locallyCompact M
  let K := lift A i '' Metric.closedBall (0 : Space n) (1/2)
  let U : Unit → Set M.Carrier := fun _ => lift A i '' Metric.ball 0 (3/4)
  have hK : IsCompact K := F05_lift_closedBall_isCompact hA i (by norm_num)
  have hU : ∀ j, IsOpen (U j) := fun _ => F05_lift_ball_isOpen hA i (by norm_num)
  have hCover : K ⊆ ⋃ j, U j := by
    rintro x ⟨z,hz,rfl⟩
    exact mem_iUnion.mpr ⟨(),z,Metric.closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 3/4) hz,rfl⟩
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ,Space n)) hK.isClosed U hU hCover
  refine ⟨p (),Yau.LeafProofs.L18Aux.smoothFn_of_contMDiff_real (p ()).contMDiff,
    fun x => ⟨p.nonneg () x,p.le_one () x⟩,?_,?_⟩
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := hp () hx
    exact ⟨z,Metric.ball_subset_closedBall hz,rfl⟩
  · intro z hz
    have hSum := p.sum_eq_one (show lift A i z ∈ K from ⟨z,hz,rfl⟩)
    simpa [finsum_eq_sum_of_fintype] using hSum

end Yau.Proofs.F05Aux
