import Yau.LeafProofs.L05PucciHarnackDyadicPartition

open Set
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_grid_side_coarse (h0 : ℝ) {k l : ℕ} (hkl : k ≤ l) :
    harnackGridSide h0 k=(2 : ℝ)^(l-k)*harnackGridSide h0 l := by
  have hAdd : k+(l-k)=l := by omega
  have hFine : harnackGridSide h0 l=harnackGridSide h0 k/(2 : ℝ)^(l-k) := by
    calc
      _ = harnackGridSide h0 (k+(l-k)) := by rw [hAdd]
      _ = _ := harnack_grid_side_add h0 k (l-k)
  rw [hFine]
  field_simp

theorem harnack_grid_time_coarse (h0 : ℝ) {k l : ℕ} (hkl : k ≤ l) :
    (harnackGridSide h0 k)^2=(4 : ℝ)^(l-k)*(harnackGridSide h0 l)^2 := by
  rw [harnack_grid_side_coarse h0 hkl,mul_pow]
  have hPow : ((2 : ℝ)^(l-k))^2=(4 : ℝ)^(l-k) := by
    rw [← pow_mul,Nat.mul_comm (l-k) 2,pow_mul]
    norm_num
  rw [hPow]

theorem harnack_grid_box_eq_product {n : ℕ} (h0 : ℝ) (k : ℕ) (i : Yau.RIdx n → ℤ) (j : ℤ) :
    harnackGridBox h0 k i j = harnackGridCube h0 k i ×ˢ
      Ioc ((j : ℝ)*(harnackGridSide h0 k)^2) (((j : ℝ)+1)*(harnackGridSide h0 k)^2) := by
  unfold harnackGridBox harnackGridBottom
  congr 2
  ring

theorem harnack_grid_box_ancestor {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) {k l : ℕ} (hkl : k ≤ l)
    (i : Yau.RIdx n → ℤ) (j : ℤ) :
    harnackGridBox h0 l i j ⊆ harnackGridBox h0 k
      (fun q => i q/(2 : ℤ)^(l-k)) (j/(4 : ℤ)^(l-k)) := by
  rw [harnack_grid_box_eq_product,harnack_grid_box_eq_product]
  apply Set.prod_mono
  · intro x hx q
    have hh := harnack_grid_Ico_parent (harnack_grid_side_pos h0pos l).le (i q)
      ((2 : ℤ)^(l-k)) (pow_pos (by norm_num) _) (hx q)
    simpa only [Int.cast_pow,Int.cast_ofNat,← harnack_grid_side_coarse h0 hkl,mem_Ico] using hh
  · intro t ht
    have hh := harnack_grid_Ioc_parent (sq_nonneg (harnackGridSide h0 l)) j
      ((4 : ℤ)^(l-k)) (pow_pos (by norm_num) _) ht
    simpa only [Int.cast_pow,Int.cast_ofNat,← harnack_grid_time_coarse h0 hkl] using hh

theorem harnack_grid_ancestor_contains {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (k : ℕ) (hk : k ≤ Q.1) :
    harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 (harnackGridAncestor k Q) :=
  harnack_grid_box_ancestor h0pos hk Q.2.1 Q.2.2

theorem harnack_grid_parent_eq_ancestor {n : ℕ} (Q : harnackGridIndex n) (hQ : 0 < Q.1) :
    harnackGridParent Q = harnackGridAncestor (Q.1-1) Q := by
  have hDiff : Q.1-(Q.1-1)=1 := by omega
  simp only [harnackGridParent,harnackGridAncestor,hDiff,pow_one]

theorem harnack_grid_parent_contains {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (hQ : 0 < Q.1) :
    harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 (harnackGridParent Q) := by
  rw [harnack_grid_parent_eq_ancestor Q hQ]
  exact harnack_grid_ancestor_contains h0pos Q (Q.1-1) (Nat.sub_le _ _)

theorem harnack_grid_same_level_eq_of_inter {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q P : harnackGridIndex n) (hLevel : Q.1=P.1)
    (hInter : (harnackGridNodeBox h0 Q ∩ harnackGridNodeBox h0 P).Nonempty) : Q=P := by
  by_contra hne
  exact hInter.ne_empty (Set.disjoint_iff_inter_eq_empty.mp
    (harnack_grid_node_same_level_disjoint h0pos Q P hLevel hne))

theorem harnack_grid_nested_of_levels_inter {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q P : harnackGridIndex n) (hLevel : Q.1 ≤ P.1)
    (hInter : (harnackGridNodeBox h0 Q ∩ harnackGridNodeBox h0 P).Nonempty) :
    harnackGridNodeBox h0 P ⊆ harnackGridNodeBox h0 Q := by
  have hInc := harnack_grid_ancestor_contains h0pos P Q.1 hLevel
  have hEq : Q=harnackGridAncestor Q.1 P := by
    apply harnack_grid_same_level_eq_of_inter h0pos Q (harnackGridAncestor Q.1 P) rfl
    obtain ⟨z,hzQ,hzP⟩ := hInter
    exact ⟨z,hzQ,hInc hzP⟩
  rw [hEq]
  exact hInc

theorem harnack_grid_disjoint_or_nested {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q P : harnackGridIndex n) :
    Disjoint (harnackGridNodeBox h0 Q) (harnackGridNodeBox h0 P) ∨
      harnackGridNodeBox h0 Q ⊆ harnackGridNodeBox h0 P ∨
      harnackGridNodeBox h0 P ⊆ harnackGridNodeBox h0 Q := by
  by_cases hd : Disjoint (harnackGridNodeBox h0 Q) (harnackGridNodeBox h0 P)
  · exact Or.inl hd
  · have hInter : (harnackGridNodeBox h0 Q ∩ harnackGridNodeBox h0 P).Nonempty :=
      Set.not_disjoint_iff.mp hd
    rcases le_total Q.1 P.1 with hl|hl
    · exact Or.inr (Or.inr (harnack_grid_nested_of_levels_inter h0pos Q P hl hInter))
    · exact Or.inr (Or.inl (harnack_grid_nested_of_levels_inter h0pos P Q hl
        (by simpa only [inter_comm] using hInter)))

end Yau.LeafProofs.L05Aux
