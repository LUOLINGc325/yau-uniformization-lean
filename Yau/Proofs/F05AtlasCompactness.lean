import Yau.Proofs.F05ModelGeometry
import Yau.Proofs.F05AtlasHomeomorph

/-! The genuine finite physical atlas itself supplies the compact closure
and original open domain used by the compact maximum principle. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05ModelOpen_mem_iff (A : AtlasData M) (i : Fin A.count) (z : Space n) :
    z ∈ F05ModelOpen A i ↔ match A.normal i with | none => True | some j => realCoord z j < 0 := by
  unfold F05ModelOpen
  cases A.normal i <;> rfl

theorem F05_atlas_closure_compact {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) : IsCompact (closure O) := by
  have hUnion : IsCompact (⋃ i : Fin A.count,lift A i '' Metric.closedBall 0 1) :=
    isCompact_iUnion (fun i => F05_lift_closedBall_isCompact hA i (by norm_num : (1 : ℝ) < 3))
  apply hUnion.of_isClosed_subset isClosed_closure
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hA.2.1 hx)
  obtain ⟨z,hz,heq⟩ := hi
  exact mem_iUnion.mpr ⟨i,z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1,heq⟩

theorem F05_atlas_domain_isOpen {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) : IsOpen O := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA (subset_closure hx)
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 i
  have hzModel : z ∈ F05ModelOpen A i := (F05ModelOpen_mem_iff A i z).mpr
    ((hPhysical z (F05D_mem_ball hz)).1.mp (by rwa [heq]))
  let V := Metric.ball (0 : Space n) 3 ∩ F05ModelOpen A i
  have hV : IsOpen V := Metric.isOpen_ball.inter (F05ModelOpen_isOpen A i)
  have hImage : IsOpen (lift A i '' V) := by
    rw [← F05AtlasEquiv_inverse hA i]
    apply (F05AtlasEquiv hA i).symm.isOpen_image_of_subset_source hV
    rw [OpenPartialHomeomorph.symm_source,F05AtlasEquiv_target]
    exact inter_subset_left
  have hxImage : x ∈ lift A i '' V := ⟨z,⟨F05D_mem_ball hz,hzModel⟩,heq⟩
  apply mem_of_superset (hImage.mem_nhds hxImage)
  rintro y ⟨w,hw,rfl⟩
  exact (hPhysical w hw.1).1.mpr ((F05ModelOpen_mem_iff A i w).mp hw.2)

end Yau.Proofs.F05Aux
