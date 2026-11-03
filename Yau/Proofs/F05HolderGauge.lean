import Yau.Proofs.F05FlatRegions
import Yau.LeafProofs.L16HalfSpaceHolderExtension

/-! Signed flat-face geometry for the buffered boundary Hölder argument.
The full-space gauge is the constant one; distance to a frontier is used
only for the genuine half-space. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05CapOpen (k : Option (RIdx n)) (r : ℝ) : Set (Space n) :=
  F05FlatOpen k ∩ Metric.ball 0 r

def F05FaceGauge (k : Option (RIdx n)) (x : Space n) : ℝ :=
  match k with
  | none => 1
  | some j => -realCoord x j

def F05FaceProjection (j : RIdx n) : Space n →L[ℝ] Space n :=
  halfSpaceBoundaryProjection (realVec j)

theorem F05FaceProjection_apply (j : RIdx n) (x : Space n) :
    F05FaceProjection j x = x-realCoord x j • realVec j := by
  rw [F05FaceProjection,halfSpaceBoundaryProjection_apply (realVec_norm j),
    real_inner_comm,real_inner_realVec]

theorem F05FaceProjection_coordinate (j : RIdx n) (x : Space n) :
    realCoord (F05FaceProjection j x) j = 0 := by
  rw [← realCoordLinear_apply]
  exact halfSpaceBoundaryProjection_normal (realVec j) x

theorem F05FaceProjection_norm (j : RIdx n) (x : Space n) :
    ‖F05FaceProjection j x‖ ≤ ‖x‖ := by
  simpa only [F05FaceProjection,map_zero,sub_zero] using
    halfSpaceBoundaryProjection_nonexpansive (realVec j) x 0

theorem F05FaceProjection_distance (j : RIdx n) (x : Space n)
    (hx : realCoord x j ≤ 0) :
    ‖x-F05FaceProjection j x‖ = F05FaceGauge (some j) x := by
  rw [F05FaceProjection,halfSpaceBoundaryProjection_distance (realVec_norm j),
    real_inner_comm,real_inner_realVec,abs_of_nonpos hx]
  rfl

theorem F05FaceGauge_lipschitz (k : Option (RIdx n)) (x y : Space n) :
    |F05FaceGauge k x-F05FaceGauge k y| ≤ ‖x-y‖ := by
  cases k with
  | none => simp [F05FaceGauge]
  | some j =>
    have h := realCoord_abs_le_norm (x-y) j
    rw [← realCoordLinear_apply j, map_sub] at h
    simpa only [F05FaceGauge,realCoordLinear_apply,neg_sub_neg,abs_sub_comm] using h

theorem F05FaceGauge_nonneg {k : Option (RIdx n)} {x : Space n}
    (hx : x ∈ closure (F05FlatOpen k)) : 0 ≤ F05FaceGauge k x := by
  rw [F05FlatOpen_closure] at hx
  cases k with
  | none => norm_num [F05FaceGauge]
  | some j => exact neg_nonneg.mpr hx

theorem F05FaceGauge_pos {k : Option (RIdx n)} {x : Space n}
    (hx : x ∈ F05FlatOpen k) : 0 < F05FaceGauge k x := by
  cases k with
  | none => norm_num [F05FaceGauge]
  | some j => exact neg_pos.mpr hx

theorem F05FlatOpen_isOpen (k : Option (RIdx n)) : IsOpen (F05FlatOpen k) := by
  cases k with
  | none => exact isOpen_univ
  | some j =>
    simpa only [F05FlatOpen,realCoordLinear_apply] using
      (isOpen_lt (realCoordLinear j).continuous continuous_const :
        IsOpen {z : Space n | realCoordLinear j z < 0})

theorem F05CapOpen_isOpen (k : Option (RIdx n)) (r : ℝ) :
    IsOpen (F05CapOpen k r) := (F05FlatOpen_isOpen k).inter Metric.isOpen_ball

theorem F05FaceProjection_frontier (j : RIdx n) (x : Space n) :
    F05FaceProjection j x ∈ frontier (F05FlatOpen (some j)) := by
  rw [show F05FlatOpen (some j) = {z : Space n | realCoord z j < 0} from rfl,
    coordinate_halfSpace_frontier]
  exact F05FaceProjection_coordinate j x

theorem F05FaceGauge_infDist (j : RIdx n) (x : Space n)
    (hx : x ∈ closure (F05FlatOpen (some j))) :
    Metric.infDist x (frontier (F05FlatOpen (some j))) = F05FaceGauge (some j) x := by
  have hx' : realCoord x j ≤ 0 := by
    simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hx
  have hPlane : (frontier (F05FlatOpen (some j))).Nonempty :=
    ⟨F05FaceProjection j 0,F05FaceProjection_frontier j 0⟩
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := x) (F05FaceProjection_frontier j x)
    simpa only [dist_eq_norm,F05FaceProjection_distance j x hx'] using h
  · apply (Metric.le_infDist hPlane).mpr
    intro y hy
    rw [show F05FlatOpen (some j) = {z : Space n | realCoord z j < 0} from rfl,
      coordinate_halfSpace_frontier] at hy
    change realCoord y j = 0 at hy
    have h := F05FaceGauge_lipschitz (some j) x y
    simpa only [F05FaceGauge,hy,neg_zero,sub_zero,abs_of_nonneg (neg_nonneg.mpr hx'),
      dist_eq_norm] using h

theorem F05FaceGauge_ball_subset {k : Option (RIdx n)} {x : Space n} {r : ℝ}
    (hx : x ∈ F05FlatOpen k) (hr : r ≤ F05FaceGauge k x) :
    Metric.ball x r ⊆ F05FlatOpen k := by
  intro y hy
  cases k with
  | none => trivial
  | some j =>
    have hxy : ‖x-y‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hy
    have h := (le_abs_self (F05FaceGauge (some j) x-F05FaceGauge (some j) y)).trans
      (F05FaceGauge_lipschitz (some j) x y)
    change realCoord y j < 0
    change r ≤ -realCoord x j at hr
    dsimp only [F05FaceGauge] at h
    linarith

end Yau.Proofs.F05Aux
