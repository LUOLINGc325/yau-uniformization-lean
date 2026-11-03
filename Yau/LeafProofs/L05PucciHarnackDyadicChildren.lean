import Yau.LeafProofs.L05PucciHarnackDyadicNesting

open Set
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

abbrev harnackGridChildDigits (n : ℕ) := (Yau.RIdx n → Fin 2) × Fin 4

def harnackGridChild {n : ℕ} (Q : harnackGridIndex n) (e : harnackGridChildDigits n) : harnackGridIndex n :=
  (Q.1+1,(fun q => 2*Q.2.1 q+(e.1 q : ℕ)),4*Q.2.2+(e.2 : ℕ))

theorem harnack_grid_ediv_digit (p : ℤ) {b : ℕ} (hb : 0 < b) (e : Fin b) :
    ((b : ℤ)*p+(e : ℕ))/(b : ℤ)=p := by
  rw [Int.mul_add_ediv_left p (e : ℤ) (by exact_mod_cast hb.ne')]
  rw [Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast e.isLt),add_zero]

theorem harnack_grid_parent_child {n : ℕ} (Q : harnackGridIndex n) (e : harnackGridChildDigits n) :
    harnackGridParent (harnackGridChild Q e)=Q := by
  apply Prod.ext (by simp only [harnackGridParent,harnackGridChild,Nat.add_sub_cancel_right])
  apply Prod.ext
  · funext q
    exact harnack_grid_ediv_digit (Q.2.1 q) (by norm_num : 0 < (2 : ℕ)) (e.1 q)
  · exact harnack_grid_ediv_digit Q.2.2 (by norm_num : 0 < (4 : ℕ)) e.2

theorem harnack_grid_child_injective {n : ℕ} (Q : harnackGridIndex n) :
    Function.Injective (harnackGridChild Q) := by
  intro e f hef
  apply Prod.ext
  · funext q
    apply Fin.ext
    have hh := congrArg (fun R : harnackGridIndex n => R.2.1 q) hef
    change 2*Q.2.1 q+(e.1 q : ℕ)=2*Q.2.1 q+(f.1 q : ℕ) at hh
    omega
  · apply Fin.ext
    have hh := congrArg (fun R : harnackGridIndex n => R.2.2) hef
    change 4*Q.2.2+(e.2 : ℕ)=4*Q.2.2+(f.2 : ℕ) at hh
    omega

theorem harnack_grid_children_disjoint {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) (e f : harnackGridChildDigits n) (hne : e ≠ f) :
    Disjoint (harnackGridNodeBox h0 (harnackGridChild Q e)) (harnackGridNodeBox h0 (harnackGridChild Q f)) :=
  harnack_grid_node_same_level_disjoint h0pos _ _ rfl
    (fun h => hne (harnack_grid_child_injective Q h))

/-- The finite computed children partition their parent exactly. -/
theorem harnack_grid_children_partition {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0)
    (Q : harnackGridIndex n) :
    harnackGridNodeBox h0 Q = ⋃ e : harnackGridChildDigits n, harnackGridNodeBox h0 (harnackGridChild Q e) := by
  ext p
  constructor
  · intro hp
    let R := harnackGridContainingNode h0 (Q.1+1) p
    have hRp : p ∈ harnackGridNodeBox h0 R := harnack_grid_containing_node_mem h0pos _ p
    have hRlevel : 0 < R.1 := by change 0 < Q.1+1; omega
    have hParentEq : harnackGridParent R=Q := by
      apply harnack_grid_same_level_eq_of_inter h0pos (harnackGridParent R) Q
        (by simp only [harnackGridParent,R,harnackGridContainingNode,Nat.add_sub_cancel_right])
      exact ⟨p,harnack_grid_parent_contains h0pos R hRlevel hRp,hp⟩
    let eSpace : Yau.RIdx n → Fin 2 := fun q => ⟨(R.2.1 q%2).toNat,by
      have hLow := Int.emod_nonneg (R.2.1 q) (by decide : (2 : ℤ) ≠ 0)
      have hHigh := Int.emod_lt_of_pos (R.2.1 q) (by decide : (0 : ℤ) < 2)
      omega⟩
    let eTime : Fin 4 := ⟨(R.2.2%4).toNat,by
      have hLow := Int.emod_nonneg R.2.2 (by decide : (4 : ℤ) ≠ 0)
      have hHigh := Int.emod_lt_of_pos R.2.2 (by decide : (0 : ℤ) < 4)
      omega⟩
    have hChildEq : harnackGridChild Q (eSpace,eTime)=R := by
      apply Prod.ext (show (harnackGridChild Q (eSpace,eTime)).1=R.1 from rfl)
      apply Prod.ext
      · funext q
        have hDiv := congrArg (fun S : harnackGridIndex n => S.2.1 q) hParentEq
        have hEq := Int.mul_ediv_add_emod (R.2.1 q) 2
        have hLow := Int.emod_nonneg (R.2.1 q) (by decide : (2 : ℤ) ≠ 0)
        change 2*Q.2.1 q+((R.2.1 q%2).toNat : ℤ)=R.2.1 q
        rw [Int.toNat_of_nonneg hLow]
        change R.2.1 q/2=Q.2.1 q at hDiv
        rwa [hDiv] at hEq
      · have hDiv := congrArg (fun S : harnackGridIndex n => S.2.2) hParentEq
        have hEq := Int.mul_ediv_add_emod R.2.2 4
        have hLow := Int.emod_nonneg R.2.2 (by decide : (4 : ℤ) ≠ 0)
        change 4*Q.2.2+((R.2.2%4).toNat : ℤ)=R.2.2
        rw [Int.toNat_of_nonneg hLow]
        change R.2.2/4=Q.2.2 at hDiv
        rwa [hDiv] at hEq
    exact mem_iUnion.mpr ⟨(eSpace,eTime),by rwa [hChildEq]⟩
  · intro hp
    obtain ⟨e,he⟩ := mem_iUnion.mp hp
    have hInc := harnack_grid_parent_contains h0pos (harnackGridChild Q e)
      (show 0 < Q.1+1 by omega)
    rw [harnack_grid_parent_child] at hInc
    exact hInc he

theorem harnack_grid_children_card (n : ℕ) :
    Fintype.card (harnackGridChildDigits n)=2^(2*n)*4 := by
  simp only [harnackGridChildDigits,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Yau.RIdx,Fintype.card_prod,Fintype.card_fin]
  congr 2
  omega

end Yau.LeafProofs.L05Aux
