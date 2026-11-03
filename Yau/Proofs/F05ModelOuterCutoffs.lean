import Yau.Proofs.F05OuterCutoffs
import Yau.Proofs.F05CanonicalRegularity

/-! The genuine outer manifold cutoff has an actual smooth compact model
representative, equal to the original pull throughout the radius-three chart. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ModelOuterCutoff (A : AtlasData M) (i : Fin A.count) (β : M.Carrier → ℝ) : Space n → ℝ :=
  fun z => outerPatchBump 1 zero_lt_one 0 z * β (lift A i z)

theorem F05_outer_pull_nonzero_norm {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4)) {z : Space n}
    (hz : z ∈ Metric.ball 0 3) (hne : β (lift A i z) ≠ 0) : ‖z‖ ≤ 3/4 := by
  obtain ⟨w,hw,heq⟩ := hSupport (subset_tsupport β hne)
  have hw3 : w ∈ Metric.ball 0 3 := Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hw
  have hwz := F05_lift_injOn hA i hw3 hz heq
  simpa only [hwz,Metric.mem_closedBall,dist_zero_right] using hw

theorem F05ModelOuterCutoff_eq {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4)) {z : Space n}
    (hz : z ∈ Metric.ball 0 3) : F05ModelOuterCutoff A i β z = β (lift A i z) := by
  by_cases hne : β (lift A i z) = 0
  · simp only [F05ModelOuterCutoff,hne,mul_zero]
  have hn := F05_outer_pull_nonzero_norm hA i hSupport hz hne
  have hOne : outerPatchBump 1 zero_lt_one (0 : Space n) z = 1 :=
    (outerPatchBump 1 zero_lt_one (0 : Space n)).one_of_mem_closedBall
      (by simpa only [outerPatchBump,Metric.mem_closedBall,dist_zero_right] using
        hn.trans (by norm_num : (3/4 : ℝ) ≤ 3*1/2))
  simp only [F05ModelOuterCutoff,hOne,one_mul]

theorem F05ModelOuterCutoff_tsupport {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4)) :
    tsupport (F05ModelOuterCutoff A i β) ⊆ Metric.closedBall 0 (3/4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hMul : outerPatchBump 1 zero_lt_one (0 : Space n) z * β (lift A i z) ≠ 0 := hz
  have hPhi := (mul_ne_zero_iff.mp hMul).1
  have hBeta := (mul_ne_zero_iff.mp hMul).2
  have hn := outerPatchBump_nonzero_norm_lt zero_lt_one hPhi
  have hz3 : z ∈ Metric.ball 0 3 := by
    rw [Metric.mem_ball,dist_zero_right]
    simp only [sub_zero,mul_one] at hn
    linarith
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    F05_outer_pull_nonzero_norm hA i hSupport hz3 hBeta

theorem F05ModelOuterCutoff_contDiff {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ} (hβ : SmoothFn β) :
    ContDiff ℝ ∞ (F05ModelOuterCutoff A i β) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let φ := outerPatchBump 1 zero_lt_one (0 : Space n)
  by_cases hz : z ∈ tsupport φ
  · have hz3 : z ∈ Metric.ball 0 3 := by
      have hh : z ∈ Metric.closedBall (0 : Space n) (2*1) := by
        simpa only [φ,ContDiffBump.tsupport_eq,outerPatchBump] using hz
      exact Metric.closedBall_subset_ball (by norm_num : 2*(1 : ℝ) < 3) hh
    exact φ.contDiff.contDiffAt.mul
      ((F05_smooth_function_pull_contDiffOn hA i β hβ).contDiffAt (Metric.isOpen_ball.mem_nhds hz3))
  · have hφzero : (φ : Space n → ℝ) =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
    have hZero : F05ModelOuterCutoff A i β =ᶠ[𝓝 z] 0 := by
      filter_upwards [hφzero] with w hw
      change φ w * β (lift A i w) = 0
      rw [hw,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hZero

theorem F05ModelOuterCutoff_plateau {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A i '' Metric.closedBall 0 (3/4))
    (hOne : ∀ z ∈ Metric.closedBall (0 : Space n) (1/2), β (lift A i z) = 1)
    {z : Space n} (hz : z ∈ Metric.closedBall 0 (1/2)) : F05ModelOuterCutoff A i β z = 1 := by
  rw [F05ModelOuterCutoff_eq hA i hSupport
    (Metric.closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 3) hz)]
  exact hOne z hz

end Yau.Proofs.F05Aux
