import Yau.Geometry.Basic

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- A genuine affine solution chart for all row equations. The free
coordinates omit the chosen pivot, so their dimension is exactly smaller. -/
def affineSchurRows (a : ι → ℂ) (pivot : ι) (rhs : Fin m → ℂ)
    (T : Fin m → {l : ι // l ≠ pivot} → ℂ) (i : Fin m) (l : ι) : ℂ :=
  if h : l = pivot then (rhs i - ∑ q : {l : ι // l ≠ pivot}, T i q * a q.1) / a pivot
  else T i ⟨l, h⟩

theorem affineSchurRows_satisfy (a : ι → ℂ) (pivot : ι) (ha : a pivot ≠ 0)
    (rhs : Fin m → ℂ) (T : Fin m → {l : ι // l ≠ pivot} → ℂ) (i : Fin m) :
    (∑ l, affineSchurRows a pivot rhs T i l * a l) = rhs i := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ pivot]
  have hp : affineSchurRows a pivot rhs T i pivot =
      (rhs i - ∑ q : {l : ι // l ≠ pivot}, T i q * a q.1) / a pivot := by
    simp [affineSchurRows]
  rw [hp]
  have hr : (∑ q : {l : ι // l ≠ pivot},
      affineSchurRows a pivot rhs T i q.1 * a q.1) =
      ∑ q : {l : ι // l ≠ pivot}, T i q * a q.1 := by
    apply Finset.sum_congr rfl
    intro q _
    simp only [affineSchurRows, dif_neg q.2]
  rw [hr, div_mul_cancel₀ _ ha]
  ring

theorem affineSchurRows_cover (a : ι → ℂ) (pivot : ι) (ha : a pivot ≠ 0)
    (rhs : Fin m → ℂ) (T : Fin m → ι → ℂ)
    (hT : ∀ i, (∑ l, T i l * a l) = rhs i) :
    T = affineSchurRows a pivot rhs (fun i q => T i q.1) := by
  funext i l
  by_cases hl : l = pivot
  · subst l
    rw [affineSchurRows, dif_pos rfl]
    change T i pivot = (rhs i - ∑ q : {l : ι // l ≠ pivot}, T i q.1 * a q.1) / a pivot
    apply (eq_div_iff ha).mpr
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun l => T i l * a l) pivot
    rw [hT i] at hs
    exact eq_sub_of_add_eq hs.symm
  · simp only [affineSchurRows, dif_neg hl]

theorem exists_pivot_pairing_of_span_top {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : ι → V) (hv : Submodule.span ℂ (range v) = ⊤)
    (ξ : V →ₗ[ℂ] ℂ) (hξ : ξ ≠ 0) : ∃ i, ξ (v i) ≠ 0 := by
  by_contra! hn
  have hs : Submodule.span ℂ (range v) ≤ LinearMap.ker ξ :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hn i)
  rw [hv] at hs
  apply hξ
  ext x
  exact hs (Submodule.mem_top)

end Yau.NodeProofs.P03Aux
