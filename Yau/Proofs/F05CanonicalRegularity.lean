import Yau.Proofs.F05CanonicalValue
import Yau.Proofs.F05Transitions

/-! The explicit manifold sum is spatially C2 at every physical chart point.
The proof only uses actual smooth coordinate transitions where a partition
factor is supported, and an actual zero neighbourhood elsewhere. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_function_pull_contDiffOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (j : Fin A.count) (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    ContDiffOn ℝ ∞ (fun z => f (lift A j z)) (Metric.ball 0 3) := by
  change ContDiffOn ℝ ∞ ((inChart (A.center j) f) ∘ A.inverse j) (Metric.ball 0 3)
  exact (hf (A.center j)).comp (hA.1 j).2.2.2.1
    (fun z hz => (hA.1 j).2.1 ((hA.1 j).2.2.2.2.1 ⟨z,hz,rfl⟩))

theorem F05CanonicalJetFunction_spatial_C2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05CompatibleJetGraph A α hT.le)
    (j : Fin A.count) {z : Space n} (hz : z ∈ F05D A j) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiffAt ℝ 2 (fun w => F05CanonicalJetFunction A χ α hT.le u (lift A j w) t) z := by
  have hz3 := F05D_mem_ball hz
  have hLift : ContinuousAt (lift A j) z := by
    rw [← F05AtlasEquiv_inverse hA j]
    apply (F05AtlasEquiv hA j).continuousAt_symm
    rw [F05AtlasEquiv_target]
    exact hz3
  have hx := F05D_lift_mem_closure hA hz
  have hTerm (i : Fin A.count) : ContDiffAt ℝ 2
      (fun w => χ i (lift A j w) * F05LocalJetExtension A i (F05InnerPlateau n)
        (u.val i).val (F05Coord A i (lift A j w),t)) z := by
    by_cases hSupport : lift A j z ∈ tsupport (χ i)
    · obtain ⟨w,hw,hwx⟩ := hχ.2.2.1 i hSupport
      have hn : ‖w‖ ≤ 1/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      have hw3 : w ∈ Metric.ball (0 : Space n) 3 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hn.trans_lt (by norm_num : (1/4 : ℝ) < 3)
      obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 i
      have hFace := (hPhysical w hw3).2.1
      rw [hwx] at hFace
      have hwD : w ∈ F05D A i := ⟨hn.trans (by norm_num),hFace.mp hx⟩
      let p : F05OverlapPoint A T := ⟨j,i,⟨z,hz⟩,⟨w,hwD⟩,⟨t,ht⟩,hwx.symm⟩
      have hTransition : ContDiffAt ℝ 2 (F05Transition A j i) z :=
        (F05Transition_overlap_contDiffAt hA p).of_le (by simp)
      let ui : F05LocalFTCGraph A i α hT.le := ⟨(u.val i).val,(u.val i).property.1.1.1⟩
      have hExtension := F05_local_extension_jets A i α hT ui (F05InnerPlateau n)
        F05InnerPlateau_contDiff F05InnerPlateau_tsupport
      have hOuter : ContDiffAt ℝ 2
          (fun w => F05LocalJetExtension A i (F05InnerPlateau n) (u.val i).val (w,t))
          (F05Transition A j i z) :=
        hExtension.1.2.2.2.2.1 (F05Transition A j i z,t) ⟨mem_univ _,ht⟩
      have hχAt := (F05_smooth_function_pull_contDiffOn hA j (χ i) (hχ.1 i)).contDiffAt
        (Metric.isOpen_ball.mem_nhds hz3)
      have hProduct := (hχAt.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).mul (hOuter.comp z hTransition)
      unfold F05Transition at hProduct
      exact hProduct
    · have hNear : ∀ᶠ w in 𝓝 z, χ i (lift A j w) = 0 := by
        apply (hLift.tendsto.eventually ((isClosed_tsupport (χ i)).isOpen_compl.mem_nhds hSupport)).mono
        intro w hw
        exact image_eq_zero_of_notMem_tsupport hw
      have hZero : (fun w => χ i (lift A j w) * F05LocalJetExtension A i (F05InnerPlateau n)
          (u.val i).val (F05Coord A i (lift A j w),t)) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [hNear] with w hw
        rw [hw,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hZero
  unfold F05CanonicalJetFunction
  exact ContDiffAt.sum (s := Finset.univ) (fun i _ => hTerm i)

end Yau.Proofs.F05Aux
