import Yau.Proofs.F05Paths

/-! The physical closed chart regions have full-dimensional one-sided
derivatives, including their true boundary and artificial outer rim. -/

open Set Filter
open scoped Topology
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05D_isClosed (A : AtlasData M) (i : Fin A.count) : IsClosed (F05D A i) := by
  cases hν : A.normal i with
  | none =>
    have heq : F05D A i = Metric.closedBall (0 : Space n) 2 := by
      ext z
      simp [F05D,region,hν,Metric.mem_closedBall,dist_zero_right]
    rw [heq]
    exact Metric.isClosed_closedBall
  | some j =>
    have heq : F05D A i = Metric.closedBall (0 : Space n) 2 ∩
        {z | realCoordLinear j z ≤ 0} := by
      ext z
      simp [F05D,region,hν,Metric.mem_closedBall,dist_zero_right,realCoordLinear_apply]
    rw [heq]
    exact Metric.isClosed_closedBall.inter (isClosed_le (realCoordLinear j).continuous continuous_const)

theorem F05D_interior_nonempty (A : AtlasData M) (i : Fin A.count) :
    (interior (F05D A i)).Nonempty := by
  cases hν : A.normal i with
  | none =>
    refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
    apply mem_of_superset (Metric.ball_mem_nhds (0 : Space n) zero_lt_one)
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    refine ⟨hn.le.trans (by norm_num),?_⟩
    simp only [F05D,region,hν] at *
  | some j =>
    let a : Space n := -realVec j
    let V : Set (Space n) := {z | ‖z‖ < 2 ∧ realCoordLinear j z < 0}
    have hV : IsOpen V := (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt (realCoordLinear j).continuous continuous_const)
    have ha : a ∈ V := by
      constructor
      · simp [a,realVec_norm]
      · change realCoordLinear j (-realVec j) < 0
        rw [map_neg]
        change - inner ℝ (realVec j) (realVec j) < 0
        rw [realVec_inner]
        norm_num
    have hSub : V ⊆ F05D A i := by
      intro z hz
      refine ⟨hz.1.le,?_⟩
      simpa only [F05D,region,hν,realCoordLinear_apply] using hz.2.le
    exact ⟨a,mem_interior_iff_mem_nhds.mpr (mem_of_superset (hV.mem_nhds ha) hSub)⟩

theorem F05D_uniqueDiffOn (A : AtlasData M) (i : Fin A.count) : UniqueDiffOn ℝ (F05D A i) :=
  uniqueDiffOn_convex (F05D_convex A i) (F05D_interior_nonempty A i)

end Yau.Proofs.F05Aux
