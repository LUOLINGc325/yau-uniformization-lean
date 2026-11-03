import Mathlib

noncomputable section
open scoped NNReal

namespace Yau.NodeProofs.P01Aux

variable {E : Type*} [MetricSpace E]

theorem finite_radial_interpolation
    (hrad : ∀ (x y : E) {r : ℝ}, 0 ≤ r → r ≤ dist x y →
      ∃ z : E, dist x z = r ∧ dist z y = dist x y - r)
    (S : Finset ℝ≥0) :
    ∀ (o y : E), (∀ t ∈ S, (t : ℝ) ≤ dist o y) →
      ∃ f : ℝ≥0 → E,
        (∀ t ∈ S, dist o (f t) = (t : ℝ) ∧
          dist (f t) y = dist o y - (t : ℝ)) ∧
        (∀ s ∈ S, ∀ t ∈ S,
          dist (f s) (f t) = |(t : ℝ) - (s : ℝ)|) := by
  classical
  refine Finset.induction_on_max S ?_ ?_
  · intro o y hbound
    refine ⟨fun _ => o, ?_, ?_⟩
    · simp
    · simp
  · intro a S hlt ih o y hbound
    have hltR : ∀ t ∈ S, (t : ℝ) < (a : ℝ) := by
      intro t ht
      exact_mod_cast hlt t ht
    have ha : (a : ℝ) ≤ dist o y :=
      hbound a (Finset.mem_insert_self a S)
    obtain ⟨z, hoz, hzy⟩ := hrad o y a.property ha
    have hbound' : ∀ t ∈ S, (t : ℝ) ≤ dist o z := by
      intro t ht
      rw [hoz]
      exact (hltR t ht).le
    obtain ⟨f, hfEnd, hfPair⟩ := ih o z hbound'
    let f' : ℝ≥0 → E := fun t => if t = a then z else f t
    have hnew : f' a = z := by simp [f']
    have hold : ∀ t ∈ S, f' t = f t := by
      intro t ht
      have hne : t ≠ a := ne_of_lt (hlt t ht)
      simp [f', hne]
    refine ⟨f', ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · rw [hnew]
        exact ⟨hoz, hzy⟩
      · rw [hold t ht]
        have hfo := (hfEnd t ht).1
        have hfz := (hfEnd t ht).2
        have hlow := dist_triangle o (f t) y
        have hupp := dist_triangle (f t) z y
        refine ⟨hfo, ?_⟩
        linarith
    · intro s hs t ht
      rcases Finset.mem_insert.mp hs with hsEq | hsOld
      · subst s
        rcases Finset.mem_insert.mp ht with htEq | htOld
        · subst t
          simp
        · rw [hnew, hold t htOld, dist_comm z (f t), (hfEnd t htOld).2, hoz,
            abs_of_nonpos (sub_nonpos.mpr (hltR t htOld).le)]
          exact (neg_sub (t : ℝ) (a : ℝ)).symm
      · rcases Finset.mem_insert.mp ht with htEq | htOld
        · subst t
          rw [hold s hsOld, hnew, (hfEnd s hsOld).2, hoz,
            abs_of_nonneg (sub_nonneg.mpr (hltR s hsOld).le)]
          rfl
        · rw [hold s hsOld, hold t htOld]
          exact hfPair s hsOld t htOld

end Yau.NodeProofs.P01Aux
