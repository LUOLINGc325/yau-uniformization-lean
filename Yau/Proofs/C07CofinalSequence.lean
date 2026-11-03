import Mathlib

open Filter

namespace Yau.Proofs.C07Aux

/-- An arbitrarily late violation can be selected along strictly increasing
physical times that tend to infinity and stay past a prescribed threshold. -/
theorem cofinal_strictMono_sequence {P : ℝ → Prop}
    (h : ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ P t) (T₀ : ℝ) :
    ∃ tk : ℕ → ℝ, StrictMono tk ∧ Tendsto tk atTop atTop ∧
      ∀ j, T₀ ≤ tk j ∧ (j : ℝ) ≤ tk j ∧ P (tk j) := by
  classical
  choose τ hτ using h
  let tk : ℕ → ℝ := Nat.rec (τ (max T₀ 0))
    (fun j t => τ (max (t + 1) (j + 1 : ℝ)))
  have hstep (j : ℕ) : tk j + 1 ≤ tk (j + 1) := by
    change tk j + 1 ≤ τ (max (tk j + 1) (j + 1 : ℝ))
    exact (le_max_left _ _).trans (hτ _).1
  have hstrict : StrictMono tk := strictMono_nat_of_lt_succ (fun j => by
    have hh := hstep j
    linarith)
  have hall (j : ℕ) : T₀ ≤ tk j ∧ (j : ℝ) ≤ tk j ∧ P (tk j) := by
    induction j with
    | zero =>
      simp only [Nat.cast_zero]
      change T₀ ≤ τ (max T₀ 0) ∧ (0 : ℝ) ≤ τ (max T₀ 0) ∧ P (τ (max T₀ 0))
      exact ⟨(le_max_left _ _).trans (hτ _).1,
        (le_max_right _ _).trans (hτ _).1, (hτ _).2⟩
    | succ j hj =>
      refine ⟨hj.1.trans (hstrict.monotone (Nat.le_succ j)), ?_, ?_⟩
      · change ((j + 1 : ℕ) : ℝ) ≤ τ (max (tk j + 1) (j + 1 : ℝ))
        simpa only [Nat.cast_add, Nat.cast_one] using
          (le_max_right (tk j + 1) (j + 1 : ℝ)).trans (hτ _).1
      · change P (τ (max (tk j + 1) (j + 1 : ℝ)))
        exact (hτ _).2
  exact ⟨tk, hstrict, tendsto_atTop_mono (fun j => (hall j).2.1) tendsto_natCast_atTop_atTop, hall⟩

end Yau.Proofs.C07Aux
