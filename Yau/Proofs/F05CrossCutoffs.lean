import Yau.Proofs.F05TransitionDomains
import Yau.Proofs.F05ModelOuterCutoffs

/-! A genuine manifold cutoff pulled to any other chart has a compact
Euclidean representative supported in the actual open transition domain. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CrossCutoff (A : AtlasData M) (i : Fin A.count) (β : M.Carrier → ℝ)
    (z : Space n) : ℝ := outerPatchBump (7/5) (by norm_num) 0 z * β (lift A i z)

theorem F05CrossCutoff_tsupport_ball (A : AtlasData M) (i : Fin A.count)
    (β : M.Carrier → ℝ) : tsupport (F05CrossCutoff A i β) ⊆ Metric.closedBall 0 (14/5) := by
  have hh : tsupport (F05CrossCutoff A i β) ⊆
      tsupport (outerPatchBump (7/5) (by norm_num) (0 : Space n)) := tsupport_mul_subset_left
  simpa only [outerPatchBump,ContDiffBump.tsupport_eq,show 2*(7/5 : ℝ) = 14/5 by norm_num] using hh

theorem F05CrossCutoff_contDiff {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ} (hβ : SmoothFn β) :
    ContDiff ℝ ∞ (F05CrossCutoff A i β) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let φ := outerPatchBump (7/5) (by norm_num : (0 : ℝ) < 7/5) (0 : Space n)
  by_cases hz : z ∈ tsupport φ
  · have hz3 : z ∈ Metric.ball 0 3 := by
      have hh : z ∈ Metric.closedBall (0 : Space n) (2*(7/5)) := by
        simpa only [φ,ContDiffBump.tsupport_eq,outerPatchBump] using hz
      exact Metric.closedBall_subset_ball (by norm_num : 2*(7/5 : ℝ) < 3) hh
    exact φ.contDiff.contDiffAt.mul
      ((F05_smooth_function_pull_contDiffOn hA i β hβ).contDiffAt (Metric.isOpen_ball.mem_nhds hz3))
  · have hz0 : (φ : Space n → ℝ) =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
    have hZero : F05CrossCutoff A i β =ᶠ[𝓝 z] 0 := by
      filter_upwards [hz0] with w hw
      change φ w * β (lift A i w) = 0
      rw [hw,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hZero

theorem F05CrossCutoff_compactSupport (A : AtlasData M) (i : Fin A.count)
    (β : M.Carrier → ℝ) : HasCompactSupport (F05CrossCutoff A i β) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space n) (14/5))
    ((subset_tsupport _).trans (F05CrossCutoff_tsupport_ball A i β))

theorem F05CrossCutoff_tsupport_transition {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i j : Fin A.count) {β : M.Carrier → ℝ}
    (hβ : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4)) :
    tsupport (F05CrossCutoff A i β) ⊆ F05TransitionDomain A i j := by
  intro z hz
  have hz3 : z ∈ Metric.ball 0 3 := Metric.closedBall_subset_ball
    (by norm_num : (14/5 : ℝ) < 3) (F05CrossCutoff_tsupport_ball A i β hz)
  refine ⟨hz3,?_⟩
  have hLift : ContinuousAt (lift A i) z := by
    rw [← F05AtlasEquiv_inverse hA i]
    apply (F05AtlasEquiv hA i).continuousAt_symm
    rw [F05AtlasEquiv_target]
    exact hz3
  have hMem : lift A i z ∈ tsupport β := by
    by_contra hOut
    have hNear : ∀ᶠ w in 𝓝 z, β (lift A i w) = 0 := by
      apply (hLift.tendsto.eventually ((isClosed_tsupport β).isOpen_compl.mem_nhds hOut)).mono
      intro w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hZero : F05CrossCutoff A i β =ᶠ[𝓝 z] 0 := by
      filter_upwards [hNear] with w hw
      simp only [F05CrossCutoff,hw,mul_zero,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hZero) hz
  obtain ⟨w,hw,heq⟩ := hβ hMem
  exact ⟨w,Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hw,heq⟩

theorem F05CrossCutoff_eq {A : AtlasData M} (i : Fin A.count) (β : M.Carrier → ℝ)
    {z : Space n} (hz : ‖z‖ ≤ 21/10) : F05CrossCutoff A i β z = β (lift A i z) := by
  have hOne : outerPatchBump (7/5) (by norm_num) (0 : Space n) z = 1 :=
    (outerPatchBump (7/5) (by norm_num) (0 : Space n)).one_of_mem_closedBall
      (by simpa only [outerPatchBump,Metric.mem_closedBall,dist_zero_right,
        show 3*(7/5 : ℝ)/2 = 21/10 by norm_num] using hz)
  simp only [F05CrossCutoff,hOne,one_mul]

end Yau.Proofs.F05Aux
