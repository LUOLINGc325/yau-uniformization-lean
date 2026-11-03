import Yau.LeafProofs.L05PucciHarnackDyadicShrinking

open Set Metric
open scoped InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_norm_le_of_coordinate_bound {n : ℕ} (x : Space n) {a : ℝ} (ha : 0 ≤ a)
    (hCoord : ∀ q : Yau.RIdx n, |inner ℝ x (Yau.realVec q)| ≤ a) :
    ‖x‖ ≤ Real.sqrt (2*n)*a := by
  have hEach (q : Yau.RIdx n) : (inner ℝ (Yau.realVec q) x)^2 ≤ a^2 := by
    have hh := hCoord q
    rw [real_inner_comm] at hh
    have hh2 : |inner ℝ (Yau.realVec q) x|^2 ≤ a^2 :=
      (sq_le_sq₀ (abs_nonneg _) ha).mpr hh
    simpa only [sq_abs] using hh2
  have hSum := Finset.sum_le_sum (fun q (_ : q∈Finset.univ) => hEach q)
  have hNorm : ‖x‖^2 ≤ (2*n)*a^2 := by
    simpa only [pow_two,realVec_coordinates_norm_sq,Finset.sum_const,Finset.card_univ,
      Yau.RIdx,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat,
      mul_comm (n : ℝ) 2] using hSum
  have hSqrt := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*n)
  have hTarget : (Real.sqrt (2*n)*a)^2=(2*n)*a^2 := by rw [mul_pow,hSqrt]
  nlinarith [norm_nonneg x,mul_nonneg (Real.sqrt_nonneg (2*n)) ha]

theorem harnack_grid_side_parent (h0 : ℝ) (k : ℕ) :
    harnackGridSide h0 k=2*harnackGridSide h0 (k+1) := by
  rw [harnack_grid_side_succ]
  ring

theorem harnack_grid_centers_parent_distance {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (k : ℕ) (i : Yau.RIdx n → ℤ) :
    dist (harnackGridCenter h0 (k+1) i) (harnackGridCenter h0 k (fun q => i q/2)) ≤
      Real.sqrt (2*n)*harnackGridSide h0 (k+1)/2 := by
  rw [dist_eq_norm]
  have hr := harnack_grid_side_pos h0pos (k+1)
  have hh := harnack_norm_le_of_coordinate_bound
    (harnackGridCenter h0 (k+1) i-harnackGridCenter h0 k (fun q => i q/2)) (half_pos hr).le ?_
  · exact hh.trans_eq (by ring)
  · intro q
    rw [inner_sub_left,harnack_grid_center_coordinate,harnack_grid_center_coordinate,
      harnack_grid_side_parent h0 k]
    obtain ⟨hl,hu⟩ := harnack_grid_ediv_endpoint_bounds (i q) 2 (by norm_num)
    norm_num only [Int.cast_ofNat] at hl hu
    have hMulL := mul_le_mul_of_nonneg_right hl hr.le
    have hMulU := mul_le_mul_of_nonneg_right hu hr.le
    apply abs_le.mpr
    constructor <;> nlinarith

theorem harnack_grid_parent_time_bounds {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ) (j : ℤ) :
    harnackGridBottom h0 (k+1) j+(harnackGridSide h0 (k+1))^2 ≤
      harnackGridBottom h0 k (j/4)+(harnackGridSide h0 k)^2 ∧
    harnackGridBottom h0 k (j/4)+(harnackGridSide h0 k)^2 ≤
      harnackGridBottom h0 (k+1) j+4*(harnackGridSide h0 (k+1))^2 := by
  obtain ⟨hl,hu⟩ := harnack_grid_ediv_endpoint_bounds j 4 (by norm_num)
  norm_num only [Int.cast_ofNat] at hl hu
  have hMulL := mul_le_mul_of_nonneg_right hl (sq_nonneg (harnackGridSide h0 (k+1)))
  have hMulU := mul_le_mul_of_nonneg_right hu (sq_nonneg (harnackGridSide h0 (k+1)))
  simp only [harnackGridBottom,harnack_grid_side_parent h0 k]
  constructor <;> nlinarith

theorem harnack_grid_parent_distance_to_child_center {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (k : ℕ) (i : Yau.RIdx n → ℤ) {y : Space n}
    (hy : y ∈ harnackGridCube h0 k (fun q => i q/2)) :
    dist y (harnackGridCenter h0 (k+1) i) ≤
      (3/2 : ℝ)*Real.sqrt (2*n)*harnackGridSide h0 (k+1) := by
  have hY := harnack_cube_subset_closedBall (harnackGridCenter h0 k (fun q => i q/2))
    (harnack_grid_side_pos h0pos k).le (by rwa [← harnack_grid_cube_eq])
  rw [mem_closedBall,harnack_grid_side_parent h0 k] at hY
  have hCenters := harnack_grid_centers_parent_distance h0pos k i
  have hTriangle := dist_triangle y (harnackGridCenter h0 k (fun q => i q/2)) (harnackGridCenter h0 (k+1) i)
  rw [dist_comm (harnackGridCenter h0 k (fun q => i q/2)) (harnackGridCenter h0 (k+1) i)] at hTriangle
  linarith

theorem harnack_grid_child_parent_distance {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (k : ℕ) (i : Yau.RIdx n → ℤ) {x y : Space n}
    (hx : x ∈ harnackGridCube h0 (k+1) i) (hy : y ∈ harnackGridCube h0 k (fun q => i q/2)) :
    dist x y ≤ 2*Real.sqrt (2*n)*harnackGridSide h0 (k+1) := by
  have hX := harnack_cube_subset_closedBall (harnackGridCenter h0 (k+1) i)
    (harnack_grid_side_pos h0pos (k+1)).le (by rwa [← harnack_grid_cube_eq])
  rw [mem_closedBall] at hX
  have hY := harnack_grid_parent_distance_to_child_center h0pos k i hy
  have hTriangle := dist_triangle x (harnackGridCenter h0 (k+1) i) y
  rw [dist_comm (harnackGridCenter h0 (k+1) i) y] at hTriangle
  linarith

end Yau.LeafProofs.L05Aux
