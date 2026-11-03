import Yau.Proofs.F05CompactHolder
import Yau.Proofs.F05CoordinateCoefficients

/-! The fixed smooth geometric fields have one genuine coefficient budget
on every compact raw ball, before the Hölder exponent or terminal time.
No solution field enters these constants. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_raw_smooth_coefficient_budget {S r : ℝ} (hS : 0 < S) (hr : r < 3)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S)) :
    ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 0 < α → α < 1 → ∀ T : ℝ, T ≤ S →
      HolderBound α (cylinder (Metric.closedBall 0 r) 0 T) a M ∧
      (∀ j, HolderBound α (cylinder (Metric.closedBall 0 r) 0 T) (fun z => b z j) M) ∧
      HolderBound α (cylinder (Metric.closedBall 0 r) 0 T) R M := by
  classical
  have hK := isCompact_closedBall (0 : Space n) r
  have hConvex := convex_closedBall (0 : Space n) r
  have hSub : Metric.closedBall (0 : Space n) r ⊆ Metric.ball 0 3 :=
    Metric.closedBall_subset_ball hr
  obtain ⟨Ma,hMa,hA⟩ := F05_compact_cylinder_holder Metric.isOpen_ball hK hConvex hSub hS hab.1
  have hDrift (j : RIdx n) :=
    F05_compact_cylinder_holder Metric.isOpen_ball hK hConvex hSub hS (hab.2 j)
  choose Mb hMb hB using hDrift
  obtain ⟨MR,hMR,hSource⟩ := F05_compact_cylinder_holder Metric.isOpen_ball hK hConvex hSub hS hR
  let M : ℝ := 1+Ma+MR+∑ j,Mb j
  have hSum : 0 ≤ ∑ j,Mb j := Finset.sum_nonneg (fun j _ => (hMb j).le)
  have hM : 0 < M := by dsimp only [M]; positivity
  have haM : Ma ≤ M := by dsimp only [M]; linarith
  have hRM : MR ≤ M := by dsimp only [M]; linarith
  have hbM (j : RIdx n) : Mb j ≤ M := by
    have hSingle := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (RIdx n))) => (hMb k).le)
      (Finset.mem_univ j)
    dsimp only [M]
    linarith
  refine ⟨M,hM,?_⟩
  intro α hα hα1 T hTS
  exact ⟨holderBound_mono_const (hA α hα hα1 T hTS) haM,
    fun j => holderBound_mono_const (hB j α hα hα1 T hTS) (hbM j),
    holderBound_mono_const (hSource α hα hα1 T hTS) hRM⟩

end Yau.Proofs.F05Aux
