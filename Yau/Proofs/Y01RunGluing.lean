import Yau.Proofs.Y03FiniteRun

/-! Choose the finite or infinite solution once on each maximal regular run. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y01Aux

open Yau Yau.Blueprint Yau.Blueprint.Alignment

private theorem runStart_exists (reg : ℕ → Prop) (k : ℕ) :
    ∃ a : ℕ, ∀ r, a ≤ r → r ≤ k → reg r :=
  ⟨k + 1, fun r hr hrk => by omega⟩

def runStart (reg : ℕ → Prop) (k : ℕ) : ℕ :=
  Nat.find (runStart_exists reg k)

theorem runStart_interval (reg : ℕ → Prop) (k : ℕ) :
    ∀ r, runStart reg k ≤ r → r ≤ k → reg r :=
  Nat.find_spec (runStart_exists reg k)

theorem runStart_le {reg : ℕ → Prop} {k : ℕ} (hk : reg k) :
    runStart reg k ≤ k :=
  Nat.find_min' (runStart_exists reg k) (m := k) (fun r hr hrk => by
    have : r = k := by omega
    simpa only [this] using hk)

theorem runStart_succ {reg : ℕ → Prop} {k : ℕ} (hk : reg (k + 1)) :
    runStart reg (k + 1) = runStart reg k := by
  apply le_antisymm
  · apply Nat.find_min' (runStart_exists reg (k + 1))
    intro r har hr
    by_cases heq : r = k + 1
    · simpa only [heq] using hk
    · exact runStart_interval reg k r har (by omega)
  · apply Nat.find_min' (runStart_exists reg k)
    intro r har hr
    exact runStart_interval reg (k + 1) r har (by omega)

/-- The same left endpoint labels adjacent members of a regular run. -/
theorem runStart_eq_of_regular_pair {reg : ℕ → Prop} {k : ℕ}
    (_hk : reg k) (hk' : reg (k + 1)) :
    runStart reg k = runStart reg (k + 1) :=
  (runStart_succ hk').symm

/-- A run solution carries only the change and jump conclusions already
provided by `AlignmentRuns`; the boundary is computed from `reg`. -/
theorem alignment_solution_from_runs
    {n : ℕ} {E : Frames n} {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ}
    {reg : ℕ → Prop} {J : ℕ → ℕ} {S : ℕ → ℝ}
    (hruns : AlignmentRuns E D w reg J S) :
    ∃ (L : Changes n) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ k, reg k → ChangeAt D w J S C c L k ∧
        (reg (k + 1) → JumpAt E w L k) := by
  classical
  obtain ⟨C, c, hC, hc, hfinite, hinfinite⟩ := hruns
  have hcomponent (a : ℕ) (ha : reg a) : ∃ L : Changes n,
      ∀ k, a ≤ k → (∀ r, a ≤ r → r ≤ k → reg r) →
        ChangeAt D w J S C c L k ∧ (reg (k + 1) → JumpAt E w L k) := by
    by_cases htail : ∀ r, a ≤ r → reg r
    · obtain ⟨L, finite, subseq, hmono, hL, hfinite', hlimit⟩ := hinfinite a htail
      exact ⟨L, fun k hak _ => ⟨(hL k hak).1, fun _ => (hL k hak).2⟩⟩
    · have hex : ∃ b : ℕ, a ≤ b ∧ ¬ reg b := by
        by_contra hn
        apply htail
        intro r har
        by_contra hr
        exact hn ⟨r, har, hr⟩
      let b := Nat.find hex
      have hab : a ≤ b := (Nat.find_spec hex).1
      have hb : ¬ reg b := (Nat.find_spec hex).2
      have hab' : a < b := by
        by_contra hn
        have : b = a := by omega
        exact hb (this.symm ▸ ha)
      have hreg (r : ℕ) (har : a ≤ r) (hrb : r < b) : reg r := by
        by_contra hn
        have hmin := Nat.find_min' hex ⟨har, hn⟩
        change b ≤ r at hmin
        omega
      obtain ⟨L, hterminal, hL, hJump⟩ := hfinite a (b - a) (by omega)
        (fun r hr => hreg (a + r) (by omega) (by omega))
      refine ⟨L, ?_⟩
      intro k hak hk
      have hkb : k < b := by
        by_contra hn
        exact hb (hk b hab (by omega))
      have heq : a + (k - a) = k := Nat.add_sub_of_le hak
      refine ⟨?_, ?_⟩
      · simpa only [heq] using hL (k - a) (by omega)
      · intro hk'
        have hkb' : k + 1 < b := by
          by_contra hn
          have : k + 1 = b := by omega
          exact hb (this ▸ hk')
        simpa only [heq] using hJump (k - a) (by omega)
  choose component hcomponent using fun a => by
    by_cases ha : reg a
    · exact hcomponent a ha
    · exact ⟨(⟨fun _ => 1, fun _ => 1⟩ : Changes n), fun k hak hk =>
        False.elim (ha (hk a le_rfl hak))⟩
  let L : Changes n :=
    ⟨fun k => (component (runStart reg k)).plus k,
      fun k => (component (runStart reg k)).minus k⟩
  refine ⟨L, C, c, hC, hc, ?_⟩
  intro k hk
  have hrun := hcomponent (runStart reg k) k (runStart_le hk)
    (runStart_interval reg k)
  refine ⟨hrun.1, ?_⟩
  intro hk'
  have heq := runStart_succ hk'
  simpa only [JumpAt, alignedJump, L, heq] using hrun.2 hk'

end Yau.Proofs.Y01Aux
