import Yau.LeafProofs.L05PucciHarnackDyadicBasics

open Set
open scoped InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_box_mem_iff {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    (i : Yau.RIdx n → ℤ) (j : ℤ) (p : Point n) :
    p ∈ harnackGridBox h0 k i j ↔
      (∀ q, ⌊inner ℝ p.1 (Yau.realVec q)/harnackGridSide h0 k⌋ = i q) ∧
      ⌈p.2/(harnackGridSide h0 k)^2⌉-1 = j := by
  have hr := harnack_grid_side_pos h0pos k
  have hTop : (j : ℝ)*(harnackGridSide h0 k)^2+(harnackGridSide h0 k)^2 =
      ((j : ℝ)+1)*(harnackGridSide h0 k)^2 := by ring
  change ((∀ q, inner ℝ p.1 (Yau.realVec q) ∈
    Ico ((i q : ℝ)*harnackGridSide h0 k) (((i q : ℝ)+1)*harnackGridSide h0 k)) ∧
    p.2 ∈ Ioc ((j : ℝ)*(harnackGridSide h0 k)^2)
      ((j : ℝ)*(harnackGridSide h0 k)^2+(harnackGridSide h0 k)^2)) ↔ _
  rw [hTop,harnack_grid_Ioc_iff_ceil (sq_pos_of_pos hr)]
  simp only [harnack_grid_Ico_iff_floor hr]

def harnackGridContainingNode {n : ℕ} (h0 : ℝ) (k : ℕ) (p : Point n) : harnackGridIndex n :=
  (k,(fun q => ⌊inner ℝ p.1 (Yau.realVec q)/harnackGridSide h0 k⌋),
    ⌈p.2/(harnackGridSide h0 k)^2⌉-1)

theorem harnack_grid_containing_node_level {n : ℕ} (h0 : ℝ) (k : ℕ) (p : Point n) :
    (harnackGridContainingNode h0 k p).1 = k := rfl

theorem harnack_grid_containing_node_mem {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ) (p : Point n) :
    p ∈ harnackGridNodeBox h0 (harnackGridContainingNode h0 k p) :=
  (harnack_grid_box_mem_iff h0pos k _ _ p).mpr ⟨fun _ => rfl,rfl⟩

theorem harnack_grid_indices_eq_of_mem {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    (i : Yau.RIdx n → ℤ) (j : ℤ) {p : Point n} (hp : p ∈ harnackGridBox h0 k i j) :
    (i,j) = (harnackGridContainingNode h0 k p).2 := by
  obtain ⟨hi,hj⟩ := (harnack_grid_box_mem_iff h0pos k i j p).mp hp
  exact Prod.ext (funext (fun q => (hi q).symm)) hj.symm

theorem harnack_grid_point_partition {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ) (p : Point n) :
    ∃! ij : (Yau.RIdx n → ℤ) × ℤ, p ∈ harnackGridBox h0 k ij.1 ij.2 := by
  refine ⟨(harnackGridContainingNode h0 k p).2,harnack_grid_containing_node_mem h0pos k p,?_⟩
  intro ij hij
  exact harnack_grid_indices_eq_of_mem h0pos k ij.1 ij.2 hij

theorem harnack_grid_same_level_disjoint {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    (ij kl : (Yau.RIdx n → ℤ) × ℤ) (hne : ij ≠ kl) :
    Disjoint (harnackGridBox h0 k ij.1 ij.2) (harnackGridBox h0 k kl.1 kl.2) := by
  apply disjoint_left.mpr
  intro p hp hq
  exact hne ((harnack_grid_indices_eq_of_mem h0pos k ij.1 ij.2 hp).trans
    (harnack_grid_indices_eq_of_mem h0pos k kl.1 kl.2 hq).symm)

theorem harnack_grid_node_same_level_disjoint {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q P : harnackGridIndex n) (hLevel : Q.1 = P.1) (hne : Q ≠ P) :
    Disjoint (harnackGridNodeBox h0 Q) (harnackGridNodeBox h0 P) := by
  have hIndex : Q.2 ≠ P.2 := fun h => hne (Prod.ext hLevel h)
  simpa only [harnackGridNodeBox,hLevel] using harnack_grid_same_level_disjoint h0pos P.1 Q.2 P.2 hIndex

end Yau.LeafProofs.L05Aux
