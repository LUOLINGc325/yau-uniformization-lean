import Yau.LeafProofs.L05PucciHarnackDyadicBasics
import Mathlib.Analysis.Convex.Measure

open Set MeasureTheory
open scoped InnerProductSpace Topology
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_cube_convex {n : ℕ} (c : Space n) (r : ℝ) : Convex ℝ (harnackCube c r) := by
  intro x hx y hy a b ha hb hab q
  have hh := (convex_Ico (-(r/2)) (r/2)) (hx q) (hy q) ha hb hab
  have hEq : inner ℝ (a • x+b • y-c) (Yau.realVec q) =
      a*inner ℝ (x-c) (Yau.realVec q)+b*inner ℝ (y-c) (Yau.realVec q) := by
    simp only [inner_sub_left,inner_add_left,real_inner_smul_left]
    have hWeight := congrArg (fun t : ℝ => t*inner ℝ c (Yau.realVec q)) hab
    nlinarith [hWeight]
  change -(r/2) ≤ inner ℝ (a • x+b • y-c) (Yau.realVec q) ∧
    inner ℝ (a • x+b • y-c) (Yau.realVec q) < r/2
  rw [hEq]
  exact hh

theorem harnack_cube_frontier_null {n : ℕ} (c : Space n) (r : ℝ) :
    (volume : Measure (Space n)) (frontier (harnackCube c r))=0 :=
  (harnack_cube_convex c r).addHaar_frontier volume

theorem harnack_grid_cube_frontier_null {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) :
    (volume : Measure (Space n)) (frontier (harnackGridCube h0 k i))=0 := by
  rw [harnack_grid_cube_eq]
  exact harnack_cube_frontier_null _ _

end Yau.LeafProofs.L05Aux
