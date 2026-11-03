import Yau.Proofs.Y06ForbiddenProjection

/-! A finite backward recursion with inactive resets, proved by backward
induction. The hypotheses are explicit step and forcing inequalities. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y06Aux

def backwardValue {E : Type*} (b : ℕ) (step : ℕ → E → E) (terminal : E) (k : ℕ) : E :=
  if k < b then step k (backwardValue b step terminal (k + 1)) else terminal
termination_by b - k
decreasing_by omega

theorem backwardValue_terminal {E : Type*} (b : ℕ) (step : ℕ → E → E) (z : E)
    {k : ℕ} (hk : b ≤ k) : backwardValue b step z k = z := by
  rw [backwardValue, ite_eq_right (by omega)]

theorem backwardValue_step {E : Type*} (b : ℕ) (step : ℕ → E → E) (z : E)
    {k : ℕ} (hk : k < b) : backwardValue b step z k = step k (backwardValue b step z (k + 1)) := by
  rw [backwardValue, ite_eq_left hk]

theorem backwardValue_bound {E : Type*} (b : ℕ) (step : ℕ → E → E) (z : E)
    (ν : E → ℝ) (W : ℕ → ℝ) (hz : ν z ≤ W b)
    (hstep : ∀ k, k < b → ∀ x, ν x ≤ W (k + 1) → ν (step k x) ≤ W k) :
    ∀ k, k ≤ b → ν (backwardValue b step z k) ≤ W k := by
  intro k hk
  induction hk using Nat.decreasingInduction with
  | self => simpa only [backwardValue_terminal b step z le_rfl] using hz
  | of_succ k hk ih =>
    rw [backwardValue_step b step z hk]
    exact hstep k hk _ ih

theorem finite_backward_envelope {E : Type*} [AddMonoid E]
    (b : ℕ) (active : ℕ → Prop) (T : ℕ → E → E) (f : ℕ → E)
    (ν : E → ℝ) (a W : ℕ → ℝ) (hν0 : ν 0 = 0)
    (hadd : ∀ x y, ν (x + y) ≤ ν x + ν y) (hW : ∀ k, 0 ≤ W k)
    (ha : ∀ k, 0 ≤ a k)
    (hT : ∀ k, k < b → active k → ∀ x, ν (T k x) ≤ a k * ν x)
    (hforce : ∀ k, k < b → active k → ν (f k) ≤ W k / 2)
    (hratio : ∀ k, k < b → active k → a k * W (k + 1) ≤ W k / 2) :
    ∃ u : ℕ → E,
      (∀ k, b ≤ k → u k = 0) ∧
      (∀ k, k < b → u k = if active k then T k (u (k + 1)) + f k else 0) ∧
      ∀ k, ν (u k) ≤ W k := by
  classical
  let step := fun k x => if active k then T k x + f k else 0
  let u := backwardValue b step 0
  have hb : ∀ k, k ≤ b → ν (u k) ≤ W k := by
    apply backwardValue_bound b step 0 ν W
    · simpa only [hν0] using hW b
    · intro k hk x hx
      by_cases hact : active k
      · change ν (if active k then T k x + f k else 0) ≤ W k
        rw [ite_eq_left hact]
        have hlinear := (hT k hk hact x).trans (mul_le_mul_of_nonneg_left hx (ha k))
        have hsum := hadd (T k x) (f k)
        linarith [hratio k hk hact, hforce k hk hact]
      · simpa only [step, ite_eq_right hact, hν0] using hW k
  refine ⟨u, ?_, ?_, ?_⟩
  · intro k hk
    exact backwardValue_terminal b step 0 hk
  · intro k hk
    exact backwardValue_step b step 0 hk
  · intro k
    by_cases hk : k ≤ b
    · exact hb k hk
    · have hu : u k = 0 := backwardValue_terminal b step 0 (by omega)
      rw [hu, hν0]
      exact hW k

end Yau.Proofs.Y06Aux
