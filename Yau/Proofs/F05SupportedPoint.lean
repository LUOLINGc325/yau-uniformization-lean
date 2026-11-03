import Yau.Proofs.F05ManifoldSourcePatch

/-! A genuine supported chart factor identifies the actual physical chart
coordinate of every point of the original closed domain where it is nonzero. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_supported_coord {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (j : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {x : M.Carrier} (hx : x ∈ closure O) (hβ : β x ≠ 0) :
    F05Coord A j x ∈ F05D A j ∧ ‖F05Coord A j x‖ ≤ 3/4 ∧ lift A j (F05Coord A j x) = x := by
  obtain ⟨z,hz,heq⟩ := hSupport (subset_tsupport β hβ)
  have hn : ‖z‖ ≤ 3/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hz3 : z ∈ Metric.ball (0 : Space n) 3 := Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hz
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 j
  have hClosure := (hPhysical z hz3).2.1
  rw [heq] at hClosure
  have hzD : z ∈ F05D A j := ⟨hn.trans (by norm_num),hClosure.mp hx⟩
  have hCoord : F05Coord A j x = z := by rw [← heq,F05Coord_lift hA hzD]
  rw [hCoord]
  exact ⟨hzD,hn,heq⟩

theorem F05ManifoldPatch_initial_time {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {T : ℝ} {v : Point n → ℝ}
    (hTime0 : ∀ z ∈ closure (F05ModelOpen A j),
      timeD (cylinder (closure (F05ModelOpen A j)) 0 T) v (z,0) = 0)
    {z : Space n} (hz : z ∈ F05D A i) :
    timeD (F05Q A i T) (pull A i (F05ManifoldPatch A j β v)) (z,0) = 0 := by
  have hFiber : {t : ℝ | (z,t) ∈ F05Q A i T} = Icc 0 T := by
    ext t
    change (z ∈ F05D A i ∧ t ∈ Icc 0 T) ↔ t ∈ Icc 0 T
    exact and_iff_right hz
  unfold timeD
  rw [hFiber]
  change derivWithin (fun t => β (lift A i z)*v (F05Coord A j (lift A i z),t)) (Icc 0 T) 0 = 0
  rw [derivWithin_const_mul_field]
  by_cases hβ : β (lift A i z) = 0
  · rw [hβ,zero_mul]
  have hCoord := F05_supported_coord hA j hSupport (F05D_lift_mem_closure hA hz) hβ
  have hMem := F05D_subset_model_closure A j hCoord.1
  have hTargetFiber : {t : ℝ | (F05Coord A j (lift A i z),t) ∈
      cylinder (closure (F05ModelOpen A j)) 0 T} = Icc 0 T := by
    ext t
    change (F05Coord A j (lift A i z) ∈ closure (F05ModelOpen A j) ∧ t ∈ Icc 0 T) ↔ t ∈ Icc 0 T
    exact and_iff_right hMem
  have hZero := hTime0 _ hMem
  unfold timeD at hZero
  rw [hTargetFiber] at hZero
  rw [hZero,mul_zero]

end Yau.Proofs.F05Aux
