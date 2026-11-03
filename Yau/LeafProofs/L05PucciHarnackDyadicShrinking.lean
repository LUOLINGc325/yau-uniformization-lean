import Yau.LeafProofs.L05PucciHarnackDyadicNesting

open Set Metric Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_cube_distance {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    (i : Yau.RIdx n → ℤ) {x y : Space n}
    (hx : x ∈ harnackGridCube h0 k i) (hy : y ∈ harnackGridCube h0 k i) :
    dist x y ≤ Real.sqrt (2*n)*harnackGridSide h0 k := by
  rw [harnack_grid_cube_eq] at hx hy
  have hX := harnack_cube_subset_closedBall (harnackGridCenter h0 k i) (harnack_grid_side_pos h0pos k).le hx
  have hY := harnack_cube_subset_closedBall (harnackGridCenter h0 k i) (harnack_grid_side_pos h0pos k).le hy
  have hTriangle := dist_triangle x (harnackGridCenter h0 k i) y
  rw [mem_closedBall] at hX hY
  rw [dist_comm (harnackGridCenter h0 k i) y] at hTriangle
  linarith

def harnackGridDiameterBound (n : ℕ) (h0 : ℝ) (k : ℕ) : ℝ :=
  max (Real.sqrt (2*n)*harnackGridSide h0 k) ((harnackGridSide h0 k)^2)

theorem harnack_grid_box_distance {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    (i : Yau.RIdx n → ℤ) (j : ℤ) {p q : Point n}
    (hp : p ∈ harnackGridBox h0 k i j) (hq : q ∈ harnackGridBox h0 k i j) :
    dist p q ≤ harnackGridDiameterBound n h0 k := by
  rw [Prod.dist_eq]
  apply max_le
  · exact (harnack_grid_cube_distance h0pos k i hp.1 hq.1).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith [hp.2.1,hp.2.2,hq.2.1,hq.2.2]

theorem harnack_grid_diameter_tendsto_zero (n : ℕ) (h0 : ℝ) :
    Tendsto (harnackGridDiameterBound n h0) atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => max (Real.sqrt (2*n)*harnackGridSide h0 k)
    ((harnackGridSide h0 k)^2)) atTop (𝓝 0)
  have hSide := harnack_grid_side_tendsto_zero h0
  have h := (hSide.const_mul (Real.sqrt (2*n))).max (hSide.pow 2)
  simpa only [harnackGridDiameterBound,mul_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),max_self] using h

/-- The unique containing boxes shrink as whole sets into every open
neighborhood. This uses no differentiation or measure theorem. -/
theorem harnack_grid_fine_subset_open {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    {A : Set (Point n)} (hA : IsOpen A) {p : Point n} (hp : p ∈ A) :
    ∀ᶠ k in atTop, harnackGridNodeBox h0 (harnackGridContainingNode h0 k p) ⊆ A := by
  obtain ⟨epsilon,hEpsilon,hBall⟩ := Metric.isOpen_iff.mp hA p hp
  have hSmall : ∀ᶠ k in atTop, harnackGridDiameterBound n h0 k < epsilon :=
    (harnack_grid_diameter_tendsto_zero n h0).eventually (gt_mem_nhds hEpsilon)
  filter_upwards [hSmall] with k hk q hq
  apply hBall
  exact mem_ball.mpr ((harnack_grid_box_distance h0pos k _ _ hq
    (harnack_grid_containing_node_mem h0pos k p)).trans_lt hk)

theorem harnack_grid_fine_subset_open_exists {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    {A : Set (Point n)} (hA : IsOpen A) {p : Point n} (hp : p ∈ A) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → harnackGridNodeBox h0 (harnackGridContainingNode h0 k p) ⊆ A :=
  eventually_atTop.mp (harnack_grid_fine_subset_open h0pos hA hp)

theorem harnack_grid_index_countable (n : ℕ) : Countable (harnackGridIndex n) := inferInstance

end Yau.LeafProofs.L05Aux
