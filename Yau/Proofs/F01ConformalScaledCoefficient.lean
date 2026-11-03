import Yau.Proofs.F01ConformalLeviCoefficient

/-! A single scale-independent coefficient for the two differentiated
terms, with the actual conformal multiplier on the right. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

theorem conformalProfile_scaled_levi_coefficient (C : ℝ) (hC : 0 < C) :
    ∃ B : ℝ, 0 < B ∧ ∀ L r : ℝ, 0 < L → 0 < r → r < L →
      |deriv conformalProfile (r / L)| / L * (C / r) +
        |deriv (deriv conformalProfile) (r / L)| / L ^ 2 * C ^ 2 ≤
          (B / L ^ 2) * Real.exp (conformalProfile (r / L)) := by
  obtain ⟨A, hA, ha⟩ := conformalProfile_uniform_levi_coefficients
  let K : ℝ := C + C ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKC : C ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have hKC2 : C ^ 2 ≤ K := by dsimp [K]; linarith
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro L r hL hr hrl
  let a : ℝ := |deriv conformalProfile (r / L)| / (L * r)
  let b : ℝ := |deriv (deriv conformalProfile) (r / L)| / L ^ 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b ≤ Real.exp (conformalProfile (r / L)) * (A / L ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left (ha L r hL hr hrl)
      (Real.exp_pos (conformalProfile (r / L))).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hm
    exact hm
  have he : |deriv conformalProfile (r / L)| / L * (C / r) +
      |deriv (deriv conformalProfile) (r / L)| / L ^ 2 * C ^ 2 = C * a + C ^ 2 * b := by
    dsimp [a, b]
    field_simp [hL.ne', hr.ne']
    <;> ring
  rw [he]
  calc
    C * a + C ^ 2 * b ≤ K * a + K * b :=
      add_le_add (mul_le_mul_of_nonneg_right hKC ha0) (mul_le_mul_of_nonneg_right hKC2 hb0)
    _ = K * (a + b) := by ring
    _ ≤ K * (Real.exp (conformalProfile (r / L)) * (A / L ^ 2)) :=
      mul_le_mul_of_nonneg_left hab hK.le
    _ = (K * A / L ^ 2) * Real.exp (conformalProfile (r / L)) := by ring

end Yau.NodeProofs.F01Aux
