import Yau.Blueprint.Alignment

/-! Select each real weight threshold from one finite increasing list of old weights. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

theorem exists_ordered_cut_index {m : ℕ} (e : Fin m ↪o ℝ) (x : ℝ) :
    ∃ r : ℕ, r ≤ m ∧ ∀ i : Fin m, i.val < r ↔ e i ≤ x := by
  let S := Finset.univ.filter (fun i : Fin m => x < e i)
  by_cases hS : S.Nonempty
  · let r := S.min' hS
    have hrmem : r ∈ S := Finset.min'_mem S hS
    have hrx : x < e r := (Finset.mem_filter.1 hrmem).2
    refine ⟨r.val, r.isLt.le, ?_⟩
    intro i
    constructor
    · intro hir
      by_contra hn
      have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge hn⟩
      have hri : r ≤ i := Finset.min'_le S i hiS
      exact (not_le_of_gt hir) hri
    · intro hix
      by_contra hn
      have hri : r ≤ i := le_of_not_gt hn
      have hei : e r ≤ e i := e.monotone hri
      exact (not_le_of_gt hrx) (hei.trans hix)
  · refine ⟨m, le_rfl, ?_⟩
    intro i
    have hix : e i ≤ x := by
      by_contra hn
      exact hS ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_not_ge hn⟩⟩
    exact iff_of_true i.isLt hix

def orderedCutIndex {m : ℕ} (e : Fin m ↪o ℝ) (x : ℝ) : ℕ :=
  (exists_ordered_cut_index e x).choose

theorem orderedCutIndex_le {m : ℕ} (e : Fin m ↪o ℝ) (x : ℝ) : orderedCutIndex e x ≤ m :=
  (exists_ordered_cut_index e x).choose_spec.1

theorem orderedCutIndex_spec {m : ℕ} (e : Fin m ↪o ℝ) (x : ℝ) (i : Fin m) :
    i.val < orderedCutIndex e x ↔ e i ≤ x := (exists_ordered_cut_index e x).choose_spec.2 i

theorem orderedCutIndex_monotone {m : ℕ} (e : Fin m ↪o ℝ) : Monotone (orderedCutIndex e) := by
  intro x y hxy
  by_contra hn
  have hyx : orderedCutIndex e y < orderedCutIndex e x := lt_of_not_ge hn
  have hym : orderedCutIndex e y < m := hyx.trans_le (orderedCutIndex_le e x)
  let i : Fin m := ⟨orderedCutIndex e y, hym⟩
  have hix : e i ≤ x := (orderedCutIndex_spec e x i).1 hyx
  have hiy := (orderedCutIndex_spec e y i).2 (hix.trans hxy)
  exact (Nat.lt_irrefl _) hiy

end Yau.Blueprint.Alignment.Y03Proof
