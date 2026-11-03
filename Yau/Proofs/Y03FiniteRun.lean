import Yau.Blueprint.Alignment

/-! A genuine finite backward induction with one fixed pair of quantitative constants. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem changeAt_congr {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ} {J : ℕ → ℕ} {S : ℕ → ℝ}
    {C c : ℝ} {L L' : Changes n} {k : ℕ}
    (hp : L.plus k = L'.plus k) (hm : L.minus k = L'.minus k) :
    ChangeAt D w J S C c L k ↔ ChangeAt D w J S C c L' k := by
  simp only [ChangeAt, hp, hm]

theorem jumpAt_congr {E : Frames n} {w : ℕ → Fin n → ℝ} {L L' : Changes n} {k : ℕ}
    (hp : L.plus k = L'.plus k) (hm : L.minus (k + 1) = L'.minus (k + 1)) :
    JumpAt E w L k ↔ JumpAt E w L' k := by
  simp only [JumpAt, alignedJump, hp, hm]

theorem finite_alignment_of_local_extension (E : Frames n) (D : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (reg : ℕ → Prop) (J : ℕ → ℕ) (S : ℕ → ℝ) (C c : ℝ)
    (hbase : ∀ k, reg k → ChangeAt D w J S C c (⟨fun _ => 1, fun _ => 1⟩ : Changes n) k)
    (hext : ∀ k, reg k → reg (k + 1) → ∀ next : Changes n,
      ChangeAt D w J S C c next (k + 1) → ∃ L : Changes n,
        ChangeAt D w J S C c L k ∧ JumpAt E w L k ∧
        ∀ r, k + 1 ≤ r → L.plus r = next.plus r ∧ L.minus r = next.minus r) :
    ∀ a len : ℕ, 0 < len → (∀ r, r < len → reg (a + r)) →
      ∃ L : Changes n, L.plus (a + len - 1) = 1 ∧
        (∀ r, r < len → ChangeAt D w J S C c L (a + r)) ∧
        ∀ r, r + 1 < len → JumpAt E w L (a + r) := by
  intro a len hlen hreg
  let b := a + len - 1
  have hab : a ≤ b := by omega
  have hreg' (k : ℕ) (hk : a ≤ k) (hkb : k ≤ b) : reg k := by
    have hr : k - a < len := by omega
    simpa only [Nat.add_sub_of_le hk] using hreg (k - a) hr
  have hbuild : ∀ k, k ≤ b → a ≤ k → ∃ L : Changes n,
      L.plus b = 1 ∧ (∀ r, k ≤ r → r ≤ b → ChangeAt D w J S C c L r) ∧
        ∀ r, k ≤ r → r < b → JumpAt E w L r := by
    apply Nat.decreasingInduction
    · intro k hkb ih hak
      obtain ⟨next, hterminal, hchanges, hjumps⟩ := ih (by omega)
      obtain ⟨L, hcurrent, hjump, hfuture⟩ := hext k (hreg' k hak hkb.le)
        (hreg' (k + 1) (by omega) hkb) next (hchanges (k + 1) le_rfl hkb)
      refine ⟨L, (hfuture b hkb).1.trans hterminal, ?_, ?_⟩
      · intro r hkr hrb
        by_cases h : r = k
        · simpa only [h] using hcurrent
        · have hkr' : k + 1 ≤ r := by omega
          exact (changeAt_congr (hfuture r hkr').1 (hfuture r hkr').2).2 (hchanges r hkr' hrb)
      · intro r hkr hrb
        by_cases h : r = k
        · simpa only [h] using hjump
        · have hkr' : k + 1 ≤ r := by omega
          exact (jumpAt_congr (hfuture r hkr').1 (hfuture (r + 1) (by omega)).2).2
            (hjumps r hkr' hrb)
    · intro _
      refine ⟨⟨fun _ => 1, fun _ => 1⟩, rfl, ?_, ?_⟩
      · intro r hbr hrb
        have : r = b := by omega
        subst r
        exact hbase b (hreg' b hab le_rfl)
      · intro r hbr hrb
        omega
  obtain ⟨L, hterminal, hchanges, hjumps⟩ := hbuild a hab le_rfl
  refine ⟨L, hterminal, ?_, ?_⟩
  · intro r hr
    exact hchanges (a + r) (by omega) (by omega)
  · intro r hr
    exact hjumps (a + r) (by omega) (by omega)

end Yau.Blueprint.Alignment.Y03Proof
