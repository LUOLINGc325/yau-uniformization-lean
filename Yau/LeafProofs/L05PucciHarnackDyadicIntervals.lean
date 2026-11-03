import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

open Set
noncomputable section
namespace Yau.LeafProofs.L05Aux

/-- Exact integer indexing of a spatial half-open interval. -/
theorem harnack_grid_Ico_iff_floor {r x : ℝ} (hr : 0 < r) (i : ℤ) :
    x ∈ Ico ((i : ℝ)*r) (((i : ℝ)+1)*r) ↔ ⌊x/r⌋ = i := by
  rw [Int.floor_eq_iff]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hr).mpr hx.1,(div_lt_iff₀ hr).mpr hx.2⟩
  · intro hx
    exact ⟨(le_div_iff₀ hr).mp hx.1,(div_lt_iff₀ hr).mp hx.2⟩

/-- Time uses the opposite half-open convention, including grid tops. -/
theorem harnack_grid_Ioc_iff_ceil {r x : ℝ} (hr : 0 < r) (j : ℤ) :
    x ∈ Ioc ((j : ℝ)*r) (((j : ℝ)+1)*r) ↔ ⌈x/r⌉-1 = j := by
  have hCeil : ⌈x/r⌉-1 = j ↔ ⌈x/r⌉ = j+1 := by omega
  rw [hCeil,Int.ceil_eq_iff]
  simp only [Int.cast_add,Int.cast_one,add_sub_cancel_right]
  constructor
  · intro hx
    exact ⟨(lt_div_iff₀ hr).mpr hx.1,(div_le_iff₀ hr).mpr hx.2⟩
  · intro hx
    exact ⟨(lt_div_iff₀ hr).mp hx.1,(div_le_iff₀ hr).mp hx.2⟩

theorem harnack_grid_Ico_exists_unique {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∃! i : ℤ, x ∈ Ico ((i : ℝ)*r) (((i : ℝ)+1)*r) := by
  refine ⟨⌊x/r⌋,(harnack_grid_Ico_iff_floor hr _).mpr rfl,?_⟩
  intro i hi
  exact ((harnack_grid_Ico_iff_floor hr i).mp hi).symm

theorem harnack_grid_Ioc_exists_unique {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∃! j : ℤ, x ∈ Ioc ((j : ℝ)*r) (((j : ℝ)+1)*r) := by
  refine ⟨⌈x/r⌉-1,(harnack_grid_Ioc_iff_ceil hr _).mpr rfl,?_⟩
  intro j hj
  exact ((harnack_grid_Ioc_iff_ceil hr j).mp hj).symm

theorem harnack_grid_Ico_disjoint {r : ℝ} (hr : 0 < r) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (Ico ((i : ℝ)*r) (((i : ℝ)+1)*r)) (Ico ((j : ℝ)*r) (((j : ℝ)+1)*r)) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact hij (((harnack_grid_Ico_iff_floor hr i).mp hx).symm.trans ((harnack_grid_Ico_iff_floor hr j).mp hy))

theorem harnack_grid_Ioc_disjoint {r : ℝ} (hr : 0 < r) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (Ioc ((i : ℝ)*r) (((i : ℝ)+1)*r)) (Ioc ((j : ℝ)*r) (((j : ℝ)+1)*r)) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact hij (((harnack_grid_Ioc_iff_ceil hr i).mp hx).symm.trans ((harnack_grid_Ioc_iff_ceil hr j).mp hy))

/-- Euclidean division controls negative indices with the same inequalities. -/
theorem harnack_grid_ediv_bounds (i b : ℤ) (hb : 0 < b) :
    b*(i/b) ≤ i ∧ i < b*(i/b+1) := by
  have hEq := Int.mul_ediv_add_emod i b
  have hLow := Int.emod_nonneg i hb.ne'
  have hHigh := Int.emod_lt_of_pos i hb
  constructor <;> nlinarith

theorem harnack_grid_ediv_real_bounds (i b : ℤ) (hb : 0 < b) :
    (b : ℝ)*((i/b : ℤ) : ℝ) ≤ (i : ℝ) ∧
      (i : ℝ) < (b : ℝ)*(((i/b : ℤ) : ℝ)+1) := by
  have hh := harnack_grid_ediv_bounds i b hb
  exact ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩

end Yau.LeafProofs.L05Aux
