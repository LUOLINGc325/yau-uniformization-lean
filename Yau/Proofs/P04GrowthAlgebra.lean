import spec.CHAIN.CONTRACTS

noncomputable section
open scoped Topology

namespace Yau.Proofs.P04Aux

/-- The paper's linear growth is absorbed by its fixed three-halves power. -/
theorem linear_le_three_halves (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r →
      C * (1+r) ≤ B+1+r ^ ((3 : ℝ)/2) := by
  let a := |C|
  let B := a * (1+(a+1)^2)
  have ha : 0 ≤ a := abs_nonneg C
  have hB : a ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (a+1)]
  refine ⟨B,ha.trans hB,?_⟩
  intro r hr
  have HC : C*(1+r) ≤ a*(1+r) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  by_cases hsmall : r ≤ (a+1)^2
  · have H : a*(1+r) ≤ B := by dsimp only [B]; nlinarith
    exact HC.trans (H.trans (by linarith [Real.rpow_nonneg hr ((3 : ℝ)/2)]))
  · have hsqrt : a ≤ Real.sqrt r := by
      apply (Real.le_sqrt ha hr).mpr
      nlinarith
    have hp : r ^ ((3 : ℝ)/2) = r*Real.sqrt r := by
      rw [show (3 : ℝ)/2=1+(1/2 : ℝ) by norm_num,
        Real.rpow_add (lt_of_le_of_lt (sq_nonneg (a+1)) (lt_of_not_ge hsmall)),Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    have HH := mul_le_mul_of_nonneg_left hsqrt hr
    rw [← hp] at HH
    nlinarith

/-- Apply the preceding bound to the actual exponential growth estimate. -/
theorem exponential_linear_le_three_halves (C : ℝ) :
    ∃ B : ℝ, ∀ r : ℝ, 0 ≤ r →
      Real.exp (C*(1+r)) ≤ Real.exp B * Real.exp (1+r ^ ((3 : ℝ)/2)) := by
  obtain ⟨B,hB,H⟩ := linear_le_three_halves C
  refine ⟨B,fun r hr => ?_⟩
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa only [add_assoc] using H r hr)

/-- The zero-based geometric bound in the paper has total mass two. -/
theorem geometric_half_hasSum : HasSum (fun i : ℕ => (1/2 : ℝ)^i) 2 := by
  convert hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num) using 1 <;> norm_num

/-- This is the final scalar conversion for the majorant's allowed growth. -/
theorem log_le_three_halves {A r : ℝ} (hA : 0 < A) (hr : 0 ≤ r)
    (hbound : A ≤ 2*Real.exp (1+r ^ ((3 : ℝ)/2))) :
    Real.log A ≤ (1+Real.log 2)*(1+r ^ ((3 : ℝ)/2)) := by
  have HH := Real.log_le_log hA hbound
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _),Real.log_exp] at HH
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpow := Real.rpow_nonneg hr ((3 : ℝ)/2)
  nlinarith

end Yau.Proofs.P04Aux
