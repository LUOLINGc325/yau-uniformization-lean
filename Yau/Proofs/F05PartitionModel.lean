import Yau.Proofs.F05Atlas
import Yau.LeafProofs.L16

/-! The actual manifold partition has globally smooth Euclidean representatives
supported in the inner quarter-ball of each genuine flattened chart. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_lift_injOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) : (Metric.ball 0 3).InjOn (lift A i) := by
  rw [← F05AtlasEquiv_inverse hA i,← F05AtlasEquiv_target hA i]
  exact (F05AtlasEquiv hA i).symm.injOn

theorem F05_partition_pull_contDiffOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (fun z => χ i (lift A i z)) (Metric.ball 0 3) := by
  change ContDiffOn ℝ ∞ ((inChart (A.center i) (χ i)) ∘ A.inverse i) (Metric.ball 0 3)
  exact (hχ.1 i (A.center i)).comp (hA.1 i).2.2.2.1
    (fun z hz => (hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩))

theorem F05_partition_pull_nonzero_norm {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (i : Fin A.count) {z : Space n}
    (hz : z ∈ Metric.ball 0 3) (hne : χ i (lift A i z) ≠ 0) : ‖z‖ ≤ (1/4 : ℝ) := by
  obtain ⟨w,hw,heq⟩ := hχ.2.2.1 i (subset_tsupport (χ i) hne)
  have hwBall : w ∈ Metric.ball 0 3 :=
    (Metric.closedBall_subset_ball (by norm_num : (1/4 : ℝ) < 3)) hw
  have hwz := F05_lift_injOn hA i hwBall hz heq
  simpa only [hwz,Metric.mem_closedBall,dist_zero_right] using hw

def F05ModelPartition (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (i : Fin A.count) (z : Space n) : ℝ :=
  outerPatchBump (1/2) (by norm_num) 0 z * χ i (lift A i z)

theorem F05ModelPartition_eq {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (i : Fin A.count) {z : Space n}
    (hz : z ∈ Metric.ball 0 3) : F05ModelPartition A χ i z = χ i (lift A i z) := by
  by_cases hne : χ i (lift A i z) = 0
  · simp only [F05ModelPartition,hne,mul_zero]
  have hn := F05_partition_pull_nonzero_norm hA hχ i hz hne
  have hOne : outerPatchBump (1/2) (by norm_num) (0 : Space n) z = 1 :=
    (outerPatchBump (1/2) (by norm_num) (0 : Space n)).one_of_mem_closedBall
      (by simpa only [outerPatchBump,Metric.mem_closedBall,dist_zero_right] using
        hn.trans (by norm_num : (1/4 : ℝ) ≤ 3*(1/2)/2))
  simp only [F05ModelPartition,hOne,one_mul]

theorem F05ModelPartition_tsupport {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (i : Fin A.count) :
    tsupport (F05ModelPartition A χ i) ⊆ Metric.closedBall 0 (1/4) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hMul : outerPatchBump (1/2) (by norm_num) (0 : Space n) z * χ i (lift A i z) ≠ 0 := hz
  have hPhi := (mul_ne_zero_iff.mp hMul).1
  have hChi := (mul_ne_zero_iff.mp hMul).2
  have hn := outerPatchBump_nonzero_norm_lt (by norm_num : (0 : ℝ) < 1/2) hPhi
  have hzBall : z ∈ Metric.ball 0 3 := by
    rw [Metric.mem_ball,dist_zero_right]
    simp only [sub_zero] at hn
    linarith
  have hSmall := F05_partition_pull_nonzero_norm hA hχ i hzBall hChi
  simpa only [Metric.mem_closedBall,dist_zero_right] using hSmall

theorem F05ModelPartition_contDiff {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ}
    (hχ : F05Partition O A χ) (i : Fin A.count) : ContDiff ℝ ∞ (F05ModelPartition A χ i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  let φ := outerPatchBump (1/2) (by norm_num : (0 : ℝ) < 1/2) (0 : Space n)
  by_cases hz : z ∈ tsupport φ
  · have hzBall : z ∈ Metric.ball 0 3 := by
      have hh : z ∈ Metric.closedBall (0 : Space n) (2*(1/2)) := by
        simpa only [φ,ContDiffBump.tsupport_eq,outerPatchBump] using hz
      exact (Metric.closedBall_subset_ball (by norm_num : 2*(1/2 : ℝ) < 3)) hh
    exact φ.contDiff.contDiffAt.mul
      ((F05_partition_pull_contDiffOn hA hχ i).contDiffAt (Metric.isOpen_ball.mem_nhds hzBall))
  · have hφzero : (φ : Space n → ℝ) =ᶠ[𝓝 z] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    have hzero : F05ModelPartition A χ i =ᶠ[𝓝 z] 0 := by
      filter_upwards [hφzero] with y hy
      change φ y * χ i (lift A i y) = 0
      rw [hy,Pi.zero_apply,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem F05ModelPartition_nonneg {O : Set M.Carrier} {A : AtlasData M}
    {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (i : Fin A.count) (z : Space n) : 0 ≤ F05ModelPartition A χ i z :=
  mul_nonneg (outerPatchBump (1/2) (by norm_num) (0 : Space n)).nonneg (hχ.2.1 i _)

end Yau.Proofs.F05Aux
