import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod

/-! Exact multiplicities of differences in the square of a finite Fourier
sum. This is the triangular weight of the actual Fejer polynomial. -/

open scoped BigOperators
noncomputable section
namespace Yau.Blueprint.V04Proof

theorem fejer_difference_fiber_card (P : ℕ) (k : ℤ) :
    (((Finset.Icc (0 : ℤ) P).product (Finset.Icc (0 : ℤ) P)).filter
      (fun p => p.1 - p.2 = k)).card = ((P : ℤ) + 1 - |k|).toNat := by
  classical
  let s := ((Finset.Icc (0 : ℤ) P).product (Finset.Icc (0 : ℤ) P)).filter
    (fun p => p.1 - p.2 = k)
  let t := Finset.Icc (max 0 k) (min (P : ℤ) (P + k))
  have hc : s.card = t.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · intro p hp
      simp only [s, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hp
      simp only [t, Finset.mem_Icc, max_le_iff, le_min_iff]
      omega
    · intro p hp q hq heq
      simp only [s, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hp hq
      apply Prod.ext heq
      omega
    · intro r hr
      refine ⟨(r, r - k), ?_, rfl⟩
      simp only [t, Finset.mem_Icc, max_le_iff, le_min_iff] at hr
      simp only [s, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega
  change s.card = _
  rw [hc]
  dsimp only [t]
  rw [Int.card_Icc]
  congr 1
  by_cases hk : 0 ≤ k
  · rw [max_eq_right hk, min_eq_left (by omega : (P : ℤ) ≤ P + k), abs_of_nonneg hk]
  · have hkn : k ≤ 0 := le_of_lt (lt_of_not_ge hk)
    rw [max_eq_left hkn, min_eq_right (by omega : (P : ℤ) + k ≤ P), abs_of_nonpos hkn]
    omega

theorem fejer_difference_sum {M : Type*} [AddCommMonoid M]
    (P : ℕ) (f : ℤ → M) :
    ∑ p ∈ (Finset.Icc (0 : ℤ) P).product (Finset.Icc (0 : ℤ) P), f (p.1 - p.2) =
      ∑ k ∈ Finset.Icc (-(P : ℤ)) P, (((P : ℤ) + 1 - |k|).toNat) • f k := by
  classical
  have hmap : ∀ p ∈ (Finset.Icc (0 : ℤ) P).product (Finset.Icc (0 : ℤ) P),
      p.1 - p.2 ∈ Finset.Icc (-(P : ℤ)) P := by
    intro p hp
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Icc]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const, fejer_difference_fiber_card]

end Yau.Blueprint.V04Proof
