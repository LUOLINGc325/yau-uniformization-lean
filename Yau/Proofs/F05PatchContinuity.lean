import Yau.Proofs.F05ManifoldPatch
import Yau.LeafProofs.L18

/-! The literal supported manifold patch is jointly continuous on the full
closed time slab, including the support edge and initial face. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05AtlasEquiv_toFun {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) :
    (F05AtlasEquiv hA i : M.Carrier → Space n) = F05Coord A i := by
  funext x
  simp [F05AtlasEquiv,F05AtlasFlatten,F05Coord,chartPt,ComplexModel]

theorem F05Coord_continuousAt_image {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {x : M.Carrier}
    (hx : x ∈ lift A i '' Metric.ball 0 3) : ContinuousAt (F05Coord A i) x := by
  obtain ⟨z,hz,rfl⟩ := hx
  have hSource : lift A i z ∈ (F05AtlasEquiv hA i).source := by
    rw [← F05AtlasEquiv_inverse hA i]
    apply (F05AtlasEquiv hA i).map_target
    rw [F05AtlasEquiv_target]
    exact hz
  rw [← F05AtlasEquiv_toFun hA i]
  exact (F05AtlasEquiv hA i).continuousAt hSource

theorem F05ManifoldPatch_continuousOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hβ : SmoothFn β) (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4))
    {T : ℝ} {v : Point n → ℝ} (hv : ContinuousOn v (cylinder univ 0 T)) :
    ContinuousOn (fun p : M.Carrier × ℝ => F05ManifoldPatch A i β v p.1 p.2) (univ ×ˢ Icc 0 T) := by
  intro p hp
  by_cases hMem : p.1 ∈ tsupport β
  · obtain ⟨z,hz,heq⟩ := hSupport hMem
    have hImage : p.1 ∈ lift A i '' Metric.ball 0 3 :=
      ⟨z,Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hz,heq⟩
    have hCoord := F05Coord_continuousAt_image hA i hImage
    have hMap : ContinuousWithinAt (fun q : M.Carrier × ℝ => (F05Coord A i q.1,q.2))
        (univ ×ˢ Icc 0 T) p :=
      ((hCoord.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt).continuousWithinAt
    have hComp : ContinuousWithinAt (fun q : M.Carrier × ℝ => v (F05Coord A i q.1,q.2))
        (univ ×ˢ Icc 0 T) p :=
      (hv _ ⟨mem_univ _,hp.2⟩).comp hMap (fun q hq => ⟨mem_univ _,hq.2⟩)
    exact ((Yau.LeafProofs.L18Aux.continuous_of_smoothFn hβ).comp continuous_fst).continuousWithinAt.mul hComp
  · have hNear : ∀ᶠ q : M.Carrier × ℝ in 𝓝 p, β q.1 = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hMem).comp_tendsto continuous_fst.continuousAt
    have hZero : (fun q : M.Carrier × ℝ => F05ManifoldPatch A i β v q.1 q.2) =ᶠ[𝓝 p] 0 := by
      filter_upwards [hNear] with q hq
      simp only [F05ManifoldPatch,hq,zero_mul,Pi.zero_apply]
    exact (continuousAt_const.congr_of_eventuallyEq hZero).continuousWithinAt

end Yau.Proofs.F05Aux
