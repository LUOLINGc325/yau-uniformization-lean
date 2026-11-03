import Yau.LeafProofs.L05PucciHarnackGridData
import Yau.LeafProofs.L05PucciHarnackDyadicIntervalParent
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_side_pos {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ) : 0 < harnackGridSide h0 k :=
  div_pos h0pos (pow_pos (by norm_num) _)

theorem harnack_grid_side_succ (h0 : ℝ) (k : ℕ) :
    harnackGridSide h0 (k+1)=harnackGridSide h0 k/2 := by
  simp only [harnackGridSide,pow_succ]
  ring

theorem harnack_grid_side_add (h0 : ℝ) (k l : ℕ) :
    harnackGridSide h0 (k+l)=harnackGridSide h0 k/(2 : ℝ)^l := by
  simp only [harnackGridSide,pow_add]
  ring

theorem harnack_grid_side_tendsto_zero (h0 : ℝ) :
    Tendsto (harnackGridSide h0) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem harnack_grid_center_coordinate {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) (q : Yau.RIdx n) :
    inner ℝ (harnackGridCenter h0 k i) (Yau.realVec q)=((i q : ℝ)+1/2)*harnackGridSide h0 k := by
  have hOrth (p q : Yau.RIdx n) : inner ℝ (Yau.realVec p) (Yau.realVec q) = if p=q then 1 else 0 := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (orthonormal_iff_ite.mp (complexVector_realOrthonormalBasis n).orthonormal) p q
  simp [harnackGridCenter,sum_inner,real_inner_smul_left,hOrth]

theorem harnack_grid_cube_eq {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) :
    harnackGridCube h0 k i = harnackCube (harnackGridCenter h0 k i) (harnackGridSide h0 k) := by
  ext x
  simp only [harnackGridCube,harnackCube,mem_setOf_eq,inner_sub_left,harnack_grid_center_coordinate]
  constructor
  · intro hx q
    have h := hx q
    constructor <;> linarith
  · intro hx q
    have h := hx q
    constructor <;> linarith

theorem harnack_grid_box_eq {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) (j : ℤ) :
    harnackGridBox h0 k i j = harnackBox (harnackGridCenter h0 k i) (harnackGridSide h0 k) (harnackGridBottom h0 k j) := by
  rw [harnackGridBox,harnackBox,harnack_grid_cube_eq]

theorem harnack_grid_cube_measurable {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) :
    MeasurableSet (harnackGridCube h0 k i) := by
  rw [harnack_grid_cube_eq]
  exact harnack_cube_measurable _ _

theorem harnack_grid_box_measurable {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) (j : ℤ) :
    MeasurableSet (harnackGridBox h0 k i j) := by
  rw [harnack_grid_box_eq]
  exact harnack_box_measurable _ _ _

theorem harnack_grid_box_mu {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ) (i : Yau.RIdx n → ℤ) (j : ℤ) :
    harnackMu (harnackGridBox h0 k i j)=harnackCubeVolume n*(harnackGridSide h0 k)^(2*n+2) := by
  rw [harnack_grid_box_eq,harnack_box_mu _ (harnack_grid_side_pos h0pos k)]

end Yau.LeafProofs.L05Aux
