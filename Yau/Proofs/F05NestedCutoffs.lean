import Yau.Proofs.F05ModelOuterCutoffs

/-! Two actual nested manifold cutoffs let the outer commutator be glued
without multiplying its residual by a second nonconstant factor. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_manifold_buffer_cutoff {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {r s : ℝ} (hrs : r < s) (hs : s ≤ 3) :
    ∃ β : M.Carrier → ℝ, SmoothFn β ∧ (∀ x, 0 ≤ β x ∧ β x ≤ 1) ∧
      tsupport β ⊆ lift A i '' Metric.closedBall 0 s ∧
      ∀ z ∈ Metric.closedBall (0 : Space n) r, β (lift A i z) = 1 := by
  classical
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := Yau.LeafProofs.L12Aux.manifold_locallyCompact M
  let K := lift A i '' Metric.closedBall (0 : Space n) r
  let U : Unit → Set M.Carrier := fun _ => lift A i '' Metric.ball 0 s
  have hK : IsCompact K := F05_lift_closedBall_isCompact hA i (hrs.trans_le hs)
  have hU : ∀ j, IsOpen (U j) := fun _ => F05_lift_ball_isOpen hA i hs
  have hCover : K ⊆ ⋃ j,U j := by
    rintro x ⟨z,hz,rfl⟩
    exact mem_iUnion.mpr ⟨(),z,Metric.closedBall_subset_ball hrs hz,rfl⟩
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ,Space n)) hK.isClosed U hU hCover
  refine ⟨p (),Yau.LeafProofs.L18Aux.smoothFn_of_contMDiff_real (p ()).contMDiff,
    fun x => ⟨p.nonneg () x,p.le_one () x⟩,?_,?_⟩
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := hp () hx
    exact ⟨z,Metric.ball_subset_closedBall hz,rfl⟩
  · intro z hz
    simpa [finsum_eq_sum_of_fintype] using p.sum_eq_one (show lift A i z ∈ K from ⟨z,hz,rfl⟩)

theorem F05_nested_manifold_cutoffs {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) :
    ∃ β γ : M.Carrier → ℝ, SmoothFn β ∧ SmoothFn γ ∧
      tsupport β ⊆ lift A i '' Metric.closedBall 0 (5/8) ∧
      tsupport γ ⊆ lift A i '' Metric.closedBall 0 (3/4) ∧
      (∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A i z) = 1) ∧
      ∀ z ∈ Metric.closedBall (0 : Space n) (5/8), γ (lift A i z) = 1 := by
  obtain ⟨β,hβ,hβRange,hβSupport,hβOne⟩ := F05_manifold_buffer_cutoff hA i
    (by norm_num : (1/2 : ℝ) < 5/8) (by norm_num : (5/8 : ℝ) ≤ 3)
  obtain ⟨γ,hγ,hγRange,hγSupport,hγOne⟩ := F05_manifold_buffer_cutoff hA i
    (by norm_num : (5/8 : ℝ) < 3/4) (by norm_num : (3/4 : ℝ) ≤ 3)
  exact ⟨β,γ,hβ,hγ,hβSupport,hγSupport,hβOne,hγOne⟩

theorem F05ModelOuterCutoff_tsupport_radius {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ} {r : ℝ} (hr : r < 3)
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 r) :
    tsupport (F05ModelOuterCutoff A i β) ⊆ Metric.closedBall 0 r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hMul : outerPatchBump 1 zero_lt_one (0 : Space n) z*β (lift A i z) ≠ 0 := hz
  have hPhi := (mul_ne_zero_iff.mp hMul).1
  have hBeta := (mul_ne_zero_iff.mp hMul).2
  have hn := Yau.LeafProofs.L16Aux.outerPatchBump_nonzero_norm_lt zero_lt_one hPhi
  have hz3 : z ∈ Metric.ball (0 : Space n) 3 := by
    rw [sub_zero,mul_one] at hn
    rw [Metric.mem_ball,dist_zero_right]
    linarith
  obtain ⟨w,hw,heq⟩ := hSupport (subset_tsupport β hBeta)
  have hw3 := Metric.closedBall_subset_ball hr hw
  have hwz := F05_lift_injOn hA i hw3 hz3 heq
  rwa [hwz] at hw

end Yau.Proofs.F05Aux
