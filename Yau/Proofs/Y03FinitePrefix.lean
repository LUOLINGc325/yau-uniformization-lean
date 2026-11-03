import Yau.Proofs.Y03FiniteRun
import Yau.Proofs.Y03InverseBound

/-! Finite terminal solutions can be normalized outside their intervals with a bound uniform in every horizon. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def truncateChanges (L : Changes n) (a b : ℕ) : Changes n where
  plus := fun k => if a ≤ k ∧ k ≤ b then L.plus k else 1
  minus := fun k => if a ≤ k ∧ k ≤ b then L.minus k else 1

theorem truncateChanges_changeAt {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ}
    {J : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ} (L : Changes n) {a b k : ℕ}
    (hk : a ≤ k ∧ k ≤ b) (hL : ChangeAt D w J S C c L k) :
    ChangeAt D w J S C c (truncateChanges L a b) k := by
  exact (changeAt_congr (by simp only [truncateChanges, ite_eq_left hk])
    (by simp only [truncateChanges, ite_eq_left hk])).2 hL

theorem truncateChanges_jumpAt {E : Frames n} {w : ℕ → Fin n → ℝ} (L : Changes n) {a b k : ℕ}
    (hk : a ≤ k ∧ k ≤ b) (hk' : a ≤ k + 1 ∧ k + 1 ≤ b) (hL : JumpAt E w L k) :
    JumpAt E w (truncateChanges L a b) k := by
  exact (jumpAt_congr (by simp only [truncateChanges, ite_eq_left hk])
    (by simp only [truncateChanges, ite_eq_left hk'])).2 hL

theorem truncateChanges_plus_bound {D : ℕ → Herm n} {w : ℕ → Fin n → ℝ}
    {J : ℕ → ℕ} {S : ℕ → ℝ} {C c : ℝ} (L : Changes n) (a b : ℕ)
    (hL : ∀ k, a ≤ k → k ≤ b → ChangeAt D w J S C c L k) :
    ∀ k, matOpNorm ((truncateChanges L a b).plus k) ≤ max 1 ((1 + (J k : ℝ)) ^ C) := by
  intro k
  by_cases hk : a ≤ k ∧ k ≤ b
  · simp only [truncateChanges, ite_eq_left hk]
    have hb := (hL k hk.1 hk.2).2.2.2.2.1
    have hn : 0 ≤ matOpNorm (L.plus k)⁻¹ := norm_nonneg _
    exact (by linarith : matOpNorm (L.plus k) ≤ (1 + (J k : ℝ)) ^ C).trans (le_max_right _ _)
  · simp only [truncateChanges, ite_eq_right hk]
    exact (matOpNorm_one_le (n := n)).trans (le_max_left _ _)

theorem normalized_finite_prefix_family (E : Frames n) (D : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (reg : ℕ → Prop) (J : ℕ → ℕ) (S : ℕ → ℝ) (C c : ℝ)
    (hfinite : ∀ a len : ℕ, 0 < len → (∀ r, r < len → reg (a + r)) →
      ∃ L : Changes n, L.plus (a + len - 1) = 1 ∧
        (∀ r, r < len → ChangeAt D w J S C c L (a + r)) ∧
        ∀ r, r + 1 < len → JumpAt E w L (a + r))
    (a : ℕ) (htail : ∀ k, a ≤ k → reg k) :
    ∃ finite : ℕ → Changes n,
      (∀ H, (finite H).plus (a + H) = 1 ∧
        (∀ r, r ≤ H → ChangeAt D w J S C c (finite H) (a + r)) ∧
        ∀ r, r < H → JumpAt E w (finite H) (a + r)) ∧
      ∀ H k, matOpNorm ((finite H).plus k) ≤ max 1 ((1 + (J k : ℝ)) ^ C) := by
  have hex (H : ℕ) : ∃ L : Changes n, L.plus (a + H) = 1 ∧
      (∀ r, r ≤ H → ChangeAt D w J S C c L (a + r)) ∧
      ∀ r, r < H → JumpAt E w L (a + r) := by
    obtain ⟨L, hterm, hCh, hJu⟩ := hfinite a (H + 1) (by omega) (fun r _ => htail _ (by omega))
    have heq : a + (H + 1) - 1 = a + H := by omega
    rw [heq] at hterm
    exact ⟨L, hterm, fun r hr => hCh r (by omega), fun r hr => hJu r (by omega)⟩
  let raw := fun H => (hex H).choose
  have hraw (H : ℕ) := (hex H).choose_spec
  let finite := fun H => truncateChanges (raw H) a (a + H)
  have hInside (H k : ℕ) (hak : a ≤ k) (hkb : k ≤ a + H) : ChangeAt D w J S C c (raw H) k := by
    have heq : a + (k - a) = k := Nat.add_sub_of_le hak
    simpa only [heq] using (hraw H).2.1 (k - a) (by omega)
  refine ⟨finite, ?_, ?_⟩
  · intro H
    refine ⟨?_, ?_, ?_⟩
    · change (if a ≤ a + H ∧ a + H ≤ a + H then (raw H).plus (a + H) else 1) = 1
      rw [ite_eq_left (by omega)]
      exact (hraw H).1
    · intro r hr
      exact truncateChanges_changeAt (raw H) ⟨by omega, by omega⟩ ((hraw H).2.1 r hr)
    · intro r hr
      exact truncateChanges_jumpAt (raw H) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ((hraw H).2.2 r hr)
  · intro H k
    exact truncateChanges_plus_bound (raw H) a (a + H) (hInside H) k

end Yau.Blueprint.Alignment.Y03Proof
