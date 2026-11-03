import Yau.Proofs.Y03Grid

/-! Exact macro-window endpoints for the literal subdivided grid. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem macroClock_sub {hm : ℝ} {j N : ℕ} (hNj : N ≤ j) :
    macroClock hm (j - N) = Real.exp (-hm * N) * macroClock hm j := by
  unfold macroClock
  rw [← Real.exp_add, Nat.cast_sub hNj]
  congr 1
  ring

theorem gridClock_succ_le_macro_next (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ)
    (hhm : 0 < hm) (j₀ k : ℕ) :
    gridClock Q N M hm j₀ (k + 1) ≤ macroClock hm (macroAt Q N M hm j₀ k + 1) := by
  let j := macroAt Q N M hm j₀ k
  let p := pieces Q N M hm j
  let r := slotAt Q N M hm j₀ k
  let Δ := macroClock hm (j + 1) - macroClock hm j
  have hp : 0 < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_pieces Q N M hm j)
  have hr : (r : ℝ) + 1 ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt (slotAt_lt_pieces Q N M hm j₀ k)
  have hΔ : 0 ≤ Δ := sub_nonneg.2 ((macroClock_strictMono hm hhm).monotone (Nat.le_succ j))
  have hstep := gridClock_succ_sub Q N M hm j₀ k
  have heq : gridClock Q N M hm j₀ (k + 1) = macroClock hm j + ((r : ℝ) + 1) / p * Δ := by
    change gridClock Q N M hm j₀ (k + 1) - gridClock Q N M hm j₀ k = Δ / p at hstep
    have hcur : gridClock Q N M hm j₀ k = macroClock hm j + (r : ℝ) / p * Δ := rfl
    rw [hcur] at hstep
    calc
      _ = macroClock hm j + (r : ℝ) / p * Δ + Δ / p := by linarith
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ macroClock hm j + 1 * Δ :=
      add_le_add_right (mul_le_mul_of_nonneg_right ((div_le_one hp).2 hr) hΔ) _
    _ = macroClock hm (j + 1) := by dsimp [Δ]; ring

theorem backward_macroClock_le_scaled_gridClock (Q : ℕ → ℝ) {N : ℕ} (M : ℝ)
    {hm a₀ : ℝ} (hhm : 0 < hm) (ha₀ : 0 ≤ a₀)
    (hwindow : Real.exp (-hm * N) ≤ a₀) (j₀ k : ℕ)
    (hNj : N ≤ macroAt Q N M hm j₀ k) :
    macroClock hm (macroAt Q N M hm j₀ k - N) ≤ a₀ * gridClock Q N M hm j₀ k := by
  rw [macroClock_sub hNj]
  exact (mul_le_mul_of_nonneg_right hwindow (macroClock_pos hm _).le).trans
    (mul_le_mul_of_nonneg_left (gridClock_mem_Ico Q N M hm hhm j₀ k).1 ha₀)

end Yau.Blueprint.Alignment.Y03Proof
