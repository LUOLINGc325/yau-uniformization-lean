import Yau.Proofs.C07CofinalSequence

/-! A monotone integer index for the same physical times of an exhausting family. -/

open scoped Topology
open Filter

noncomputable section

namespace Yau.Proofs.C07Aux

open scoped Classical in
def lateIndex (T : ℕ → ℝ) (t : ℝ) : ℕ :=
  Nat.findGreatest (fun j => T j ≤ t) ⌈t⌉₊

theorem lateIndex_monotone (T : ℕ → ℝ) : Monotone (lateIndex T) := by
  classical
  intro t u htu
  exact Nat.findGreatest_mono (fun j hj => hj.trans htu) (Nat.ceil_mono htu)

theorem lateIndex_eligible (T : ℕ → ℝ) {t : ℝ} (ht : T 0 ≤ t) :
    T (lateIndex T t) ≤ t := by
  classical
  exact Nat.findGreatest_spec (P := fun j : ℕ => T j ≤ t) (n := ⌈t⌉₊) (Nat.zero_le _) ht

theorem le_lateIndex (T : ℕ → ℝ) (hmajor : ∀ j : ℕ, (j : ℝ) ≤ T j)
    {j : ℕ} {t : ℝ} (ht : T j ≤ t) : j ≤ lateIndex T t := by
  classical
  have hj : j ≤ ⌈t⌉₊ := by
    exact_mod_cast (hmajor j).trans (ht.trans (Nat.le_ceil t))
  exact Nat.le_findGreatest (P := fun j : ℕ => T j ≤ t) hj ht

theorem lateIndex_tendsto (T : ℕ → ℝ) (hmajor : ∀ j : ℕ, (j : ℝ) ≤ T j) :
    Tendsto (lateIndex T) atTop atTop := by
  apply tendsto_atTop.2
  intro j
  exact eventually_atTop.2 ⟨T j, fun t ht => le_lateIndex T hmajor ht⟩

end Yau.Proofs.C07Aux
