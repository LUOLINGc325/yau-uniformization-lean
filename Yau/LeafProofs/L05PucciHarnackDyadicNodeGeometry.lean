import Yau.LeafProofs.L05PucciHarnackDyadicParentGeometry
import Yau.LeafProofs.L05PucciHarnackDyadicBoundedRoots
import Yau.LeafProofs.L05PucciHarnackDyadicChildren
import Yau.LeafProofs.L05PucciHarnackDyadicBoundary

open Set Metric MeasureTheory
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_node_box_eq {n : ℕ} (h0 : ℝ) (Q : harnackGridIndex n) :
    harnackGridNodeBox h0 Q=harnackBox (harnackGridCenter h0 Q.1 Q.2.1)
      (harnackGridSide h0 Q.1) (harnackGridBottom h0 Q.1 Q.2.2) :=
  harnack_grid_box_eq h0 Q.1 Q.2.1 Q.2.2

theorem harnack_grid_node_box_measurable {n : ℕ} (h0 : ℝ) (Q : harnackGridIndex n) :
    MeasurableSet (harnackGridNodeBox h0 Q) := harnack_grid_box_measurable h0 Q.1 Q.2.1 Q.2.2

theorem harnack_grid_node_box_mu {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (Q : harnackGridIndex n) :
    harnackMu (harnackGridNodeBox h0 Q)=harnackCubeVolume n*(harnackGridSide h0 Q.1)^(2*n+2) :=
  harnack_grid_box_mu h0pos Q.1 Q.2.1 Q.2.2

theorem harnack_grid_node_box_mu_pos {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (Q : harnackGridIndex n) :
    0 < harnackMu (harnackGridNodeBox h0 Q) := by
  rw [harnack_grid_node_box_eq]
  exact harnack_box_mu_pos _ (harnack_grid_side_pos h0pos Q.1) _

theorem harnack_grid_node_box_measure_ne_top {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (Q : harnackGridIndex n) :
    (volume : Measure (Point n)) (harnackGridNodeBox h0 Q) ≠ ⊤ := by
  rw [harnack_grid_node_box_eq]
  exact harnack_box_measure_ne_top _ (harnack_grid_side_pos h0pos Q.1) _

theorem harnack_grid_node_box_volume {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (Q : harnackGridIndex n) :
    (volume : Measure (Point n)) (harnackGridNodeBox h0 Q)=
      ENNReal.ofReal ((harnackGridSide h0 Q.1)^(2*n+2))*
        (volume : Measure (Space n)) (harnackCube (0 : Space n) 1) := by
  rw [harnack_grid_node_box_eq]
  exact harnack_box_volume _ (harnack_grid_side_pos h0pos Q.1) _

theorem harnack_grid_cube_contains_ball {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) :
    ball (harnackGridCenter h0 k i) (harnackGridSide h0 k/2) ⊆ harnackGridCube h0 k i := by
  rw [harnack_grid_cube_eq]
  exact harnack_cube_contains_ball _

theorem harnack_grid_cube_subset_closedBall {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (k : ℕ) (i : Yau.RIdx n → ℤ) :
    harnackGridCube h0 k i ⊆ closedBall (harnackGridCenter h0 k i)
      (Real.sqrt (2*n)*harnackGridSide h0 k/2) := by
  rw [harnack_grid_cube_eq]
  exact harnack_cube_subset_closedBall _ (harnack_grid_side_pos h0pos k).le

theorem harnack_grid_node_parent_side {n : ℕ} (h0 : ℝ) (Q : harnackGridIndex n) (hQ : 0 < Q.1) :
    harnackGridSide h0 (harnackGridParent Q).1=2*harnackGridSide h0 Q.1 := by
  rcases Q with ⟨l,i,j⟩
  cases l with
  | zero => simp at hQ
  | succ k => simpa only [harnackGridParent,Nat.add_sub_cancel_right] using harnack_grid_side_parent h0 k

theorem harnack_grid_node_parent_time_bounds {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (hQ : 0 < Q.1) :
    harnackGridBottom h0 Q.1 Q.2.2+(harnackGridSide h0 Q.1)^2 ≤
      harnackGridBottom h0 (harnackGridParent Q).1 (harnackGridParent Q).2.2+
        (harnackGridSide h0 (harnackGridParent Q).1)^2 ∧
    harnackGridBottom h0 (harnackGridParent Q).1 (harnackGridParent Q).2.2+
        (harnackGridSide h0 (harnackGridParent Q).1)^2 ≤
      harnackGridBottom h0 Q.1 Q.2.2+4*(harnackGridSide h0 Q.1)^2 := by
  rcases Q with ⟨l,i,j⟩
  cases l with
  | zero => simp at hQ
  | succ k => simpa only [harnackGridParent,Nat.add_sub_cancel_right] using harnack_grid_parent_time_bounds h0pos k j

theorem harnack_grid_node_parent_distance_to_child_center {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (hQ : 0 < Q.1) {y : Space n}
    (hy : y ∈ harnackGridCube h0 (harnackGridParent Q).1 (harnackGridParent Q).2.1) :
    dist y (harnackGridCenter h0 Q.1 Q.2.1) ≤ (3/2 : ℝ)*Real.sqrt (2*n)*harnackGridSide h0 Q.1 := by
  rcases Q with ⟨l,i,j⟩
  cases l with
  | zero => simp at hQ
  | succ k => exact harnack_grid_parent_distance_to_child_center h0pos k i hy

theorem harnack_grid_node_child_parent_distance {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (hQ : 0 < Q.1) {x y : Space n}
    (hx : x ∈ harnackGridCube h0 Q.1 Q.2.1)
    (hy : y ∈ harnackGridCube h0 (harnackGridParent Q).1 (harnackGridParent Q).2.1) :
    dist x y ≤ 2*Real.sqrt (2*n)*harnackGridSide h0 Q.1 := by
  rcases Q with ⟨l,i,j⟩
  cases l with
  | zero => simp at hQ
  | succ k => exact harnack_grid_child_parent_distance h0pos k i hx hy

end Yau.LeafProofs.L05Aux
