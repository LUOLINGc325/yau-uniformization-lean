import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-! Finite polarization with labeled slots, including repeated variable values. -/

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

section Polarization

variable {A ι : Type*} [CommRing A] [DecidableEq ι]

def alternatingPowers (s : Finset ι) (x : ι → A) (q : ℕ) (b : A) : A :=
  ∑ u ∈ s.powerset, (-1 : A) ^ (s.card - u.card) * (b + ∑ a ∈ u, x a) ^ q

theorem alternatingPowers_insert (s : Finset ι) (x : ι → A) (a : ι) (ha : a ∉ s)
    (q : ℕ) (b : A) :
    alternatingPowers (insert a s) x q b =
      alternatingPowers s x q (b + x a) - alternatingPowers s x q b := by
  unfold alternatingPowers
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have hfirst : (∑ u ∈ s.powerset,
      (-1 : A) ^ (s.card + 1 - u.card) * (b + ∑ i ∈ u, x i) ^ q) =
      -(∑ u ∈ s.powerset, (-1 : A) ^ (s.card - u.card) * (b + ∑ i ∈ u, x i) ^ q) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    have hcard : u.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hu)
    rw [show s.card + 1 - u.card = (s.card - u.card) + 1 by omega, pow_succ]
    ring
  rw [hfirst]
  have hsecond : (∑ u ∈ s.powerset,
      (-1 : A) ^ (s.card + 1 - (insert a u).card) * (b + ∑ i ∈ insert a u, x i) ^ q) =
      ∑ u ∈ s.powerset,
        (-1 : A) ^ (s.card - u.card) * ((b + x a) + ∑ i ∈ u, x i) ^ q := by
    apply Finset.sum_congr rfl
    intro u hu
    have hau : a ∉ u := fun h => ha (Finset.mem_powerset.mp hu h)
    rw [Finset.card_insert_of_notMem hau, Finset.sum_insert hau, Nat.add_sub_add_right]
    congr 2
    ring
  rw [hsecond]
  ring

omit [DecidableEq ι] in
theorem alternatingPowers_shift (s : Finset ι) (x : ι → A) (q : ℕ) (b t : A) :
    alternatingPowers s x q (b + t) =
      ∑ h ∈ Finset.range (q + 1),
        ((q.choose h : ℕ) : A) * t ^ (q - h) * alternatingPowers s x h b := by
  unfold alternatingPowers
  calc
    _ = ∑ u ∈ s.powerset, ∑ h ∈ Finset.range (q + 1),
        ((q.choose h : ℕ) : A) * t ^ (q - h) *
          ((-1 : A) ^ (s.card - u.card) * (b + ∑ a ∈ u, x a) ^ h) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [show b + t + ∑ a ∈ u, x a = (b + ∑ a ∈ u, x a) + t by ring,
        add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]

theorem alternatingPowers_insert_recurrence (s : Finset ι) (x : ι → A)
    (a : ι) (ha : a ∉ s) (q : ℕ) (b : A) :
    alternatingPowers (insert a s) x q b =
      ∑ h ∈ Finset.range q,
        ((q.choose h : ℕ) : A) * x a ^ (q - h) * alternatingPowers s x h b := by
  rw [alternatingPowers_insert s x a ha, alternatingPowers_shift, Finset.sum_range_succ]
  simp

theorem alternatingPowers_le (s : Finset ι) (x : ι → A) (q : ℕ) (b : A)
    (hq : q ≤ s.card) :
    alternatingPowers s x q b =
      if q = s.card then (s.card.factorial : A) * ∏ a ∈ s, x a else 0 := by
  induction s using Finset.induction_on generalizing q b with
  | empty =>
    have hq0 : q = 0 := by simpa using hq
    subst q
    simp [alternatingPowers]
  | @insert a s ha hs =>
    rw [Finset.card_insert_of_notMem ha] at hq ⊢
    rw [alternatingPowers_insert_recurrence s x a ha]
    by_cases heq : q = s.card + 1
    · subst q
      rw [ite_eq_left rfl, Finset.sum_eq_single s.card]
      · rw [hs s.card b le_rfl, ite_eq_left rfl]
        simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, pow_one,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Finset.prod_insert ha]
        ring
      · intro h hh hne
        have hle : h ≤ s.card := by have := Finset.mem_range.mp hh; omega
        rw [hs h b hle, ite_eq_right hne]
        simp
      · simp
    · rw [ite_eq_right heq]
      apply Finset.sum_eq_zero
      intro h hh
      have hlt : h < s.card := by have := Finset.mem_range.mp hh; omega
      rw [hs h b hlt.le, ite_eq_right hlt.ne]
      simp

theorem alternatingPowers_eq_zero (s : Finset ι) (x : ι → A) (q : ℕ) (b : A)
    (hq : q < s.card) : alternatingPowers s x q b = 0 := by
  rw [alternatingPowers_le s x q b hq.le, ite_eq_right hq.ne]

theorem alternatingPowers_card (s : Finset ι) (x : ι → A) (b : A) :
    alternatingPowers s x s.card b = (s.card.factorial : A) * ∏ a ∈ s, x a := by
  rw [alternatingPowers_le s x s.card b le_rfl, ite_eq_left rfl]

theorem polarization_fin (r : ℕ) (x : Fin r → A) :
    (∑ S : Finset (Fin r), (-1 : A) ^ (r - S.card) * (∑ a ∈ S, x a) ^ r) =
      (r.factorial : A) * ∏ a, x a := by
  simpa [alternatingPowers] using alternatingPowers_card Finset.univ x 0

end Polarization

end Yau.Proofs.Y02Aux
