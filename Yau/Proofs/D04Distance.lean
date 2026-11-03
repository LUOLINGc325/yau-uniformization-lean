import Yau.Proofs.D04LocalCompactness

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau.Blueprint

@[simp] theorem erealDist_self (a : EReal) : erealDist a a = 0 := by simp [erealDist]

theorem erealDist_comm (a b : EReal) : erealDist a b = erealDist b a := by
  simp only [erealDist, eq_comm, or_left_comm, or_comm, abs_sub_comm]

@[simp] theorem erealDist_eq_zero_iff {a b : EReal} : erealDist a b = 0 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have habot : a ≠ ⊥ := by intro ha; subst a; simp [erealDist, hab] at h
    have hatop : a ≠ ⊤ := by intro ha; subst a; simp [erealDist, hab] at h
    have hbbot : b ≠ ⊥ := by intro hb; subst b; simp [erealDist, hab] at h
    have hbtop : b ≠ ⊤ := by intro hb; subst b; simp [erealDist, hab] at h
    rw [erealDist_eq_ofReal_of_finite hatop habot hbtop hbbot] at h
    have hzero : |a.toReal - b.toReal| = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp h) (abs_nonneg _)
    have hreal : a.toReal = b.toReal := sub_eq_zero.mp (abs_eq_zero.mp hzero)
    apply hab
    rw [← EReal.coe_toReal hatop habot, ← EReal.coe_toReal hbtop hbbot, hreal]
  · intro h
    subst b
    exact erealDist_self a

theorem erealDist_triangle (a b c : EReal) :
    erealDist a c ≤ erealDist a b + erealDist b c := by
  by_cases hab : a = b
  · subst b; simp
  by_cases hbc : b = c
  · subst c; simp
  by_cases hac : a = c
  · subst c; simp
  by_cases habot : a = ⊥
  · subst a; simp [erealDist, hab, hbc, hac]
  by_cases hatop : a = ⊤
  · subst a; simp [erealDist, hab, hbc, hac]
  by_cases hbbot : b = ⊥
  · subst b; simp [erealDist, hab, hbc, hac]
  by_cases hbtop : b = ⊤
  · subst b; simp [erealDist, hab, hbc, hac]
  by_cases hcbot : c = ⊥
  · subst c; simp [erealDist, hab, hbc, hac]
  by_cases hctop : c = ⊤
  · subst c; simp [erealDist, hab, hbc, hac]
  rw [erealDist_eq_ofReal_of_finite hatop habot hctop hcbot,
    erealDist_eq_ofReal_of_finite hatop habot hbtop hbbot,
    erealDist_eq_ofReal_of_finite hbtop hbbot hctop hcbot,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le a.toReal b.toReal c.toReal)

end Yau.Proofs.D04Aux
