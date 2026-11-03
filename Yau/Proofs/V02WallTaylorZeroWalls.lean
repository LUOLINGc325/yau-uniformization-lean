import Yau.Proofs.V02WallTaylorClearedKernels

/-! Cleared increments agree with the original total reciprocal and log
expressions even when one of the initial cutoff walls is zero. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

theorem cleared_wall_increments_eq {a : ℕ} (ha : 3 ≤ a) {u v u' v' Rb Rf : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hRb : |Rb| ≤ 1 / 2) (hRf : |Rf| ≤ 1 / 2)
    (heb : u' = u + (u * v) ^ a * Rb) (hef : v' = v + (u * v) ^ a * Rf) :
    ((u'⁻¹ + v'⁻¹) - (u⁻¹ + v⁻¹) =
      clearedInverseIncrement a u v Rb + clearedInverseIncrement a v u Rf) ∧
    (Real.log (u' * v') - Real.log (u * v) =
      clearedLogIncrement a u v Rb + clearedLogIncrement a v u Rf) := by
  by_cases hu0 : u = 0
  · rw [heb, hef]
    simp [hu0, clearedInverseIncrement, clearedLogIncrement, wallInverseMultiplier,
      wallRatioMultiplier, zero_pow (by omega : a ≠ 0),
      zero_pow (by omega : a - 1 ≠ 0), zero_pow (by omega : a - 2 ≠ 0)]
  by_cases hv0 : v = 0
  · rw [heb, hef]
    simp [hv0, clearedInverseIncrement, clearedLogIncrement, wallInverseMultiplier,
      wallRatioMultiplier, zero_pow (by omega : a ≠ 0),
      zero_pow (by omega : a - 1 ≠ 0), zero_pow (by omega : a - 2 ≠ 0)]
  have huP : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hvP : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
  have hbden := (wall_ratio_bounds (a := a) hu hv hRb).1
  have hfden := (wall_ratio_bounds (a := a) hv hu hRf).1
  have hb0 : 1 + wallRatioMultiplier a u v * Rb ≠ 0 := by linarith
  have hf0 : 1 + wallRatioMultiplier a v u * Rf ≠ 0 := by linarith
  have heb' : u' = u * (1 + wallRatioMultiplier a u v * Rb) := by
    rw [heb, wall_factorization (by omega : 1 ≤ a)]
  have hef' : v' = v * (1 + wallRatioMultiplier a v u * Rf) := by
    rw [hef, mul_comm u v, wall_factorization (by omega : 1 ≤ a)]
  have hu'P : 0 < u' := by rw [heb']; exact mul_pos huP (by linarith)
  have hv'P : 0 < v' := by rw [hef']; exact mul_pos hvP (by linarith)
  have hbi := reciprocal_wall_difference (by omega : 2 ≤ a) hu0 hb0
  have hfi := reciprocal_wall_difference (by omega : 2 ≤ a) hv0 hf0
  have hbl := log_wall_difference (by omega : 1 ≤ a) hu0 hb0
  have hfl := log_wall_difference (by omega : 1 ≤ a) hv0 hf0
  rw [← heb] at hbi hbl
  rw [mul_comm v u, ← hef] at hfi hfl
  constructor
  · change _ = -(wallInverseMultiplier a u v * Rb) / (1 + wallRatioMultiplier a u v * Rb) +
      -(wallInverseMultiplier a v u * Rf) / (1 + wallRatioMultiplier a v u * Rf)
    linarith
  · rw [Real.log_mul hu'P.ne' hv'P.ne', Real.log_mul hu0 hv0]
    change _ = Real.log (1 + wallRatioMultiplier a u v * Rb) +
      Real.log (1 + wallRatioMultiplier a v u * Rf)
    linarith

end Yau.Blueprint.V02WallTaylorProof
