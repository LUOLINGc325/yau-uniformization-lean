import Yau.LeafProofs.L05PucciHarnackDyadicIntervals

open Set
noncomputable section
namespace Yau.LeafProofs.L05Aux

theorem harnack_grid_ediv_endpoint_bounds (i b : ℤ) (hb : 0 < b) :
    (b : ℝ)*((i/b : ℤ) : ℝ) ≤ (i : ℝ) ∧
      (i : ℝ)+1 ≤ (b : ℝ)*(((i/b : ℤ) : ℝ)+1) := by
  obtain ⟨hl,hu⟩ := harnack_grid_ediv_bounds i b hb
  have hu' : i+1 ≤ b*(i/b+1) := by omega
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu'⟩

/-- Exact inclusion of an indexed child in its Euclidean-division parent. -/
theorem harnack_grid_Ico_parent {r : ℝ} (hr : 0 ≤ r) (i b : ℤ) (hb : 0 < b) :
    Ico ((i : ℝ)*r) (((i : ℝ)+1)*r) ⊆
      Ico (((i/b : ℤ) : ℝ)*((b : ℝ)*r)) ((((i/b : ℤ) : ℝ)+1)*((b : ℝ)*r)) := by
  obtain ⟨hl,hu⟩ := harnack_grid_ediv_endpoint_bounds i b hb
  intro x hx
  refine ⟨?_,?_⟩
  · exact (show ((i/b : ℤ) : ℝ)*((b : ℝ)*r) ≤ (i : ℝ)*r by
      convert mul_le_mul_of_nonneg_right hl hr using 1 <;> ring).trans hx.1
  · exact hx.2.trans_le (by convert mul_le_mul_of_nonneg_right hu hr using 1 <;> ring)

theorem harnack_grid_Ioc_parent {r : ℝ} (hr : 0 ≤ r) (i b : ℤ) (hb : 0 < b) :
    Ioc ((i : ℝ)*r) (((i : ℝ)+1)*r) ⊆
      Ioc (((i/b : ℤ) : ℝ)*((b : ℝ)*r)) ((((i/b : ℤ) : ℝ)+1)*((b : ℝ)*r)) := by
  obtain ⟨hl,hu⟩ := harnack_grid_ediv_endpoint_bounds i b hb
  intro x hx
  refine ⟨?_,?_⟩
  · exact (show ((i/b : ℤ) : ℝ)*((b : ℝ)*r) ≤ (i : ℝ)*r by
      convert mul_le_mul_of_nonneg_right hl hr using 1 <;> ring).trans_lt hx.1
  · exact hx.2.trans (by convert mul_le_mul_of_nonneg_right hu hr using 1 <;> ring)

/-- Every point of a parent belongs to exactly one of its finitely many
children, including negative parent indices. -/
theorem harnack_grid_Ico_children {r : ℝ} (hr : 0 < r) (p : ℤ) (b : ℕ) (hb : 0 < b) :
    Ico ((p : ℝ)*((b : ℝ)*r)) (((p : ℝ)+1)*((b : ℝ)*r)) =
      ⋃ e : Fin b, Ico ((((b : ℤ)*p+e : ℤ) : ℝ)*r)
        (((((b : ℤ)*p+e : ℤ) : ℝ)+1)*r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,-⟩ := harnack_grid_Ico_exists_unique hr x
    have hParent := harnack_grid_Ico_parent hr.le i (b : ℤ) (by exact_mod_cast hb) hi
    have hScale : 0 < (b : ℝ)*r := mul_pos (by exact_mod_cast hb) hr
    have hpi : i/(b : ℤ) = p :=
      ((harnack_grid_Ico_iff_floor hScale _).mp hParent).symm.trans ((harnack_grid_Ico_iff_floor hScale _).mp hx)
    let e : Fin b := ⟨(i%(b : ℤ)).toNat,by
      have hLow := Int.emod_nonneg i (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
      have hHigh := Int.emod_lt_of_pos i (show (0 : ℤ) < b by exact_mod_cast hb)
      omega⟩
    have he : (b : ℤ)*p+e = i := by
      have hLow := Int.emod_nonneg i (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
      simpa only [e,Int.toNat_of_nonneg hLow,hpi] using Int.mul_ediv_add_emod i (b : ℤ)
    exact mem_iUnion.mpr ⟨e,by simpa only [he] using hi⟩
  · intro hx
    obtain ⟨e,he⟩ := mem_iUnion.mp hx
    have hIdx : ((b : ℤ)*p+(e : ℕ))/(b : ℤ) = p := by
      rw [Int.mul_add_ediv_left p (e : ℤ) (by exact_mod_cast hb.ne')]
      have hSmall : ((e : ℕ) : ℤ)/(b : ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast e.isLt)
      rw [hSmall,add_zero]
    have h := harnack_grid_Ico_parent hr.le ((b : ℤ)*p+e) (b : ℤ) (by exact_mod_cast hb) he
    simpa only [hIdx,Int.cast_natCast] using h

theorem harnack_grid_Ioc_children {r : ℝ} (hr : 0 < r) (p : ℤ) (b : ℕ) (hb : 0 < b) :
    Ioc ((p : ℝ)*((b : ℝ)*r)) (((p : ℝ)+1)*((b : ℝ)*r)) =
      ⋃ e : Fin b, Ioc ((((b : ℤ)*p+e : ℤ) : ℝ)*r)
        (((((b : ℤ)*p+e : ℤ) : ℝ)+1)*r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,-⟩ := harnack_grid_Ioc_exists_unique hr x
    have hParent := harnack_grid_Ioc_parent hr.le i (b : ℤ) (by exact_mod_cast hb) hi
    have hScale : 0 < (b : ℝ)*r := mul_pos (by exact_mod_cast hb) hr
    have hpi : i/(b : ℤ) = p :=
      ((harnack_grid_Ioc_iff_ceil hScale _).mp hParent).symm.trans ((harnack_grid_Ioc_iff_ceil hScale _).mp hx)
    let e : Fin b := ⟨(i%(b : ℤ)).toNat,by
      have hLow := Int.emod_nonneg i (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
      have hHigh := Int.emod_lt_of_pos i (show (0 : ℤ) < b by exact_mod_cast hb)
      omega⟩
    have he : (b : ℤ)*p+e = i := by
      have hLow := Int.emod_nonneg i (show (b : ℤ) ≠ 0 by exact_mod_cast hb.ne')
      simpa only [e,Int.toNat_of_nonneg hLow,hpi] using Int.mul_ediv_add_emod i (b : ℤ)
    exact mem_iUnion.mpr ⟨e,by simpa only [he] using hi⟩
  · intro hx
    obtain ⟨e,he⟩ := mem_iUnion.mp hx
    have hIdx : ((b : ℤ)*p+(e : ℕ))/(b : ℤ) = p := by
      rw [Int.mul_add_ediv_left p (e : ℤ) (by exact_mod_cast hb.ne')]
      have hSmall : ((e : ℕ) : ℤ)/(b : ℤ) = 0 :=
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast e.isLt)
      rw [hSmall,add_zero]
    have h := harnack_grid_Ioc_parent hr.le ((b : ℤ)*p+e) (b : ℤ) (by exact_mod_cast hb) he
    simpa only [hIdx,Int.cast_natCast] using h

end Yau.LeafProofs.L05Aux
