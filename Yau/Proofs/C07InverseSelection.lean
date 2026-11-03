import Yau.Proofs.C07LateIndex
import Yau.Geometry.Basic

/-! Select a single inverse branch at each physical time on an increasing open exhaustion. -/

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Set

open scoped Classical in
def selectedInverseDomain {X : Type*} (V : ℕ → Set X) (T : ℕ → ℝ) (t : ℝ) : Set X :=
  if T 0 ≤ t then V (lateIndex T t) else ∅

open scoped Classical in
def selectedInverse {n : ℕ} {X : Type*} (V : ℕ → Set X) (T : ℕ → ℝ)
    (B : ℕ → ℝ → X → ComplexVector n) (t : ℝ) (x : X) : ComplexVector n :=
  if x ∈ selectedInverseDomain V T t then B (lateIndex T t) t x else 0

theorem selectedInverse_eq {n : ℕ} {X : Type*} (V : ℕ → Set X) (T : ℕ → ℝ)
    (B : ℕ → ℝ → X → ComplexVector n) {t : ℝ} {x : X}
    (hx : x ∈ selectedInverseDomain V T t) :
    selectedInverse V T B t x = B (lateIndex T t) t x := by
  simp only [selectedInverse, ite_eq_left hx]

theorem selectedInverseDomain_open {X : Type*} [TopologicalSpace X]
    (V : ℕ → Set X) (T : ℕ → ℝ) (hV : ∀ j, IsOpen (V j)) (t : ℝ) :
    IsOpen (selectedInverseDomain V T t) := by
  classical
  unfold selectedInverseDomain
  split_ifs
  · exact hV _
  · exact isOpen_empty

theorem selectedInverseDomain_monotone {X : Type*} (V : ℕ → Set X) (T : ℕ → ℝ)
    (hV : Monotone V) : Monotone (selectedInverseDomain V T) := by
  classical
  intro t u htu
  by_cases ht : T 0 ≤ t
  · simpa only [selectedInverseDomain, ite_eq_left ht, ite_eq_left (ht.trans htu)] using
      hV (lateIndex_monotone T htu)
  · simp only [selectedInverseDomain, ite_eq_right ht, empty_subset]

theorem selectedInverseDomain_exhausts {X : Type*} [TopologicalSpace X]
    (V : ℕ → Set X) (T : ℕ → ℝ) (hV : Monotone V)
    (hmajor : ∀ j : ℕ, (j : ℝ) ≤ T j)
    (hcover : ∀ K : Set X, IsCompact K → ∃ j, K ⊆ V j) :
    ∀ K : Set X, IsCompact K → ∃ S : ℝ, T 0 ≤ S ∧
      ∀ t, S ≤ t → K ⊆ selectedInverseDomain V T t := by
  classical
  intro K hK
  obtain ⟨j, hj⟩ := hcover K hK
  refine ⟨max (T 0) (T j), le_max_left _ _, ?_⟩
  intro t ht
  have ht₀ : T 0 ≤ t := (le_max_left _ _).trans ht
  have htj : T j ≤ t := (le_max_right _ _).trans ht
  simp only [selectedInverseDomain, ite_eq_left ht₀]
  exact hj.trans (hV (le_lateIndex T hmajor htj))

theorem selectedInverse_zero {n : ℕ} {X : Type*} (V : ℕ → Set X) (T : ℕ → ℝ)
    (B : ℕ → ℝ → X → ComplexVector n) (o : X) (ho : ∀ j, o ∈ V j)
    (hzero : ∀ j t, T j ≤ t → B j t o = 0) (t : ℝ) :
    selectedInverse V T B t o = 0 := by
  classical
  by_cases ht : T 0 ≤ t
  · have ho' : o ∈ selectedInverseDomain V T t := by
      simpa only [selectedInverseDomain, ite_eq_left ht] using ho (lateIndex T t)
    rw [selectedInverse_eq V T B ho']
    exact hzero _ _ (lateIndex_eligible T ht)
  · simp [selectedInverse, selectedInverseDomain, ht]

end Yau.Proofs.C07Aux
