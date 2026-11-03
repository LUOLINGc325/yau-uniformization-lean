import Yau.Proofs.C03PowerAbsorption

/-! The logarithmic source bound gives a power bound with constants
chosen before the actual map and before its two spectral values. -/

namespace Yau.Proofs.C03Aux

theorem exists_log_weight_power_bound (D S V B k M0 : ℝ)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (hB : 0 ≤ B) (hk : 0 < k) :
    ∃ P : ℝ, 0 < P ∧ ∀ A : ℝ, 0 ≤ A →
      D * Real.sqrt (2 * S ^ 2 * V + 2 * Real.exp (k * (M0 + 2 * Real.log (1 + A) + 3)) * B) ≤
        P * (1 + A) ^ k := by
  let T := Real.exp (k * (M0 + 3))
  let Q := 2 * S ^ 2 * V + 2 * T * B
  have hT : 0 < T := Real.exp_pos _
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let P := max 1 (D * Real.sqrt Q)
  refine ⟨P, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro A hA
  have hbase : 0 < 1 + A := by linarith
  have hbase1 : 1 ≤ 1 + A := by linarith
  have hp : 1 ≤ (1 + A) ^ (2 * k) := Real.one_le_rpow hbase1 (by linarith)
  have hexp : Real.exp (k * (M0 + 2 * Real.log (1 + A) + 3)) = T * (1 + A) ^ (2 * k) := by
    rw [Real.rpow_def_of_pos hbase]
    change Real.exp _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  have hsquare : Real.sqrt ((1 + A) ^ (2 * k)) = (1 + A) ^ k := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1
    ring
  have hinside : 2 * S ^ 2 * V +
      2 * Real.exp (k * (M0 + 2 * Real.log (1 + A) + 3)) * B ≤ Q * (1 + A) ^ (2 * k) := by
    rw [hexp]
    have H := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * S ^ 2 * V)
    dsimp only [Q]
    nlinarith only [H]
  calc
    D * Real.sqrt (2 * S ^ 2 * V + 2 * Real.exp (k * (M0 + 2 * Real.log (1 + A) + 3)) * B) ≤
        D * Real.sqrt (Q * (1 + A) ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) hD
    _ = (D * Real.sqrt Q) * (1 + A) ^ k := by
      rw [Real.sqrt_mul hQ, hsquare]
      ring
    _ ≤ P * (1 + A) ^ k :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hbase.le _)

end Yau.Proofs.C03Aux
