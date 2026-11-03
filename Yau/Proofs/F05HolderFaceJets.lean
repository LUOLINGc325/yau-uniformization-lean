import Yau.Proofs.F05HolderGauge
import Yau.LeafProofs.L16ExpBoundaryCombinedBarrier

/-! Exact derivatives of the inward coordinate gauge. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux
variable {n : ℕ}

theorem F05FaceGauge_some_eq (j : RIdx n) :
    F05FaceGauge (some j) = fun x => -(realCoordLinear j x) := by
  funext x
  simp only [F05FaceGauge,realCoordLinear_apply]

theorem F05FaceGauge_contDiff (k : Option (RIdx n)) : ContDiff ℝ ∞ (F05FaceGauge k) := by
  cases k with
  | none => exact contDiff_const
  | some j => rw [F05FaceGauge_some_eq]; exact (realCoordLinear j).contDiff.neg

theorem F05FaceGauge_fderiv (j : RIdx n) (x : Space n) :
    fderiv ℝ (F05FaceGauge (some j)) x = -(realCoordLinear j) := by
  rw [F05FaceGauge_some_eq,fderiv_fun_neg,(realCoordLinear j).fderiv]

theorem F05FaceGauge_fderiv_norm (j : RIdx n) (x : Space n) :
    ‖fderiv ℝ (F05FaceGauge (some j)) x‖ = 1 := by
  rw [F05FaceGauge_fderiv,norm_neg]
  exact (innerSL_apply_norm ℝ (realVec j)).trans (realVec_norm j)

theorem F05FaceGauge_secondFDeriv (j : RIdx n) (x : Space n) :
    fderiv ℝ (fderiv ℝ (F05FaceGauge (some j))) x = 0 := by
  have hEq : fderiv ℝ (F05FaceGauge (some j)) = fun _ => -(realCoordLinear j) := by
    funext y
    exact F05FaceGauge_fderiv j y
  rw [hEq]
  exact fderiv_const_apply _

theorem F05FaceGauge_zero_frontier (j : RIdx n) {x : Space n}
    (hx : x ∈ frontier (F05FlatOpen (some j))) : F05FaceGauge (some j) x = 0 := by
  rw [show F05FlatOpen (some j) = {z : Space n | realCoord z j < 0} from rfl,
    coordinate_halfSpace_frontier] at hx
  exact neg_eq_zero.mpr hx

theorem F05FaceGauge_le_norm (j : RIdx n) (x : Space n) :
    F05FaceGauge (some j) x ≤ ‖x‖ :=
  (neg_le_abs _).trans (realCoord_abs_le_norm x j)

theorem F05FaceGauge_le_dist (j : RIdx n) {x y : Space n}
    (hy : F05FaceGauge (some j) y = 0) : F05FaceGauge (some j) x ≤ ‖x-y‖ := by
  have h := (le_abs_self (F05FaceGauge (some j) x-F05FaceGauge (some j) y)).trans
    (F05FaceGauge_lipschitz (some j) x y)
  simpa only [hy,sub_zero] using h

end Yau.Proofs.F05Aux
