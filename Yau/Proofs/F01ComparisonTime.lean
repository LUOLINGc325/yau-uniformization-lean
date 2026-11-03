import spec.CHAIN.CONTRACTS

/-! Uncompiled F01 scratch time-calculus cards. All derivatives below are
actual HasDerivWithinAt data; no differential operator is caller supplied. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

variable {A : Type*}

def comparisonFunction (D : ℝ) (n : ℕ) (U P : A → ℝ → ℝ)
    (φ : A → ℝ) (x : A) (t : ℝ) : ℝ :=
  (D - t) * P x t + U x t - D * φ x + n * t

theorem comparisonFunction_initial (D : ℝ) (n : ℕ) (U P : A → ℝ → ℝ)
    (φ : A → ℝ) (hU : ∀ x, U x 0 = 0) (hP : ∀ x, P x 0 = 0) (x : A) :
    comparisonFunction D n U P φ x 0 = -D * φ x := by
  simp only [comparisonFunction, sub_zero, hP, hU, mul_zero, add_zero, zero_sub, neg_mul]

theorem comparisonFunction_hasDerivWithinAt {D dP t : ℝ} {n : ℕ}
    {U P : A → ℝ → ℝ} {φ : A → ℝ} {I : Set ℝ} (x : A)
    (hP : HasDerivWithinAt (P x) dP I t)
    (hU : HasDerivWithinAt (U x) (P x t) I t) :
    HasDerivWithinAt (comparisonFunction D n U P φ x) ((D - t) * dP + n) I t := by
  have hD : HasDerivWithinAt (fun s : ℝ => D - s) (-1) I t := by
    simpa only [id_eq] using ((hasDerivAt_id t).const_sub D).hasDerivWithinAt
  have h := (((hD.mul hP).add hU).sub_const (D * φ x)).add
    (hasDerivAt_const_mul (x := t) (n : ℝ)).hasDerivWithinAt
  unfold comparisonFunction
  convert h using 1 <;> ring

/-- The epsilon comparison is made for the SAME U,P and smooth Ξ.
This exact identity is what produces the proper quadratic barrier. -/
theorem comparisonFunction_epsilon_difference (D ε : ℝ) (n : ℕ)
    (U P : A → ℝ → ℝ) (Ξ u : A → ℝ) (C : ℝ → ℝ) (x : A) (t : ℝ) :
    comparisonFunction D n U P (fun y => Ξ y - ε * u y ^ 2 - C ε) x t -
      comparisonFunction D n U P (fun y => Ξ y - (ε / 2) * u y ^ 2 - C (ε / 2)) x t =
        (D * ε / 2) * u x ^ 2 + D * (C ε - C (ε / 2)) := by
  unfold comparisonFunction
  ring

/-- Nonnegativity of the half-epsilon comparison gives a coercive lower
bound, without any claim that its additive constant has a favorable sign. -/
theorem quadratic_lower_from_nonnegative_comparison {Q Qhalf k v b : ℝ}
    (hid : Q - Qhalf = k * v ^ 2 + b) (hhalf : 0 ≤ Qhalf) :
    k * v ^ 2 + b ≤ Q := by
  linarith

theorem positive_shifted_quadratic {Q k v b : ℝ} (hk : 0 ≤ k)
    (hQ : k * v ^ 2 + b ≤ Q) :
    0 < Q + (1 + |b|) ∧ k * v ^ 2 + 1 ≤ Q + (1 + |b|) := by
  have hb : -|b| ≤ b := neg_abs_le b
  have hp : 0 ≤ k * v ^ 2 := mul_nonneg hk (sq_nonneg _)
  constructor <;> linarith

end Yau.NodeProofs.F01Aux
