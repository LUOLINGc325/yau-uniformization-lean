import Yau.Proofs.C02FrameBounds
import Yau.Proofs.C02OperatorSmoothInverse

/-! Uniform physical bounds for the normalized inverse differential.
These are estimates for the actual inverse of the two near-identity maps. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem normalized_inverse_differential_bounds
    (D D0 : E →L[ℝ] E)
    (hD : ‖D - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4)
    (hD0 : ‖D0 - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) (v : E) :
    (1 / 3 : ℝ) * ‖v‖ ≤ ‖Real.sqrt (2 : ℝ) • D.inverse (D0 v)‖ ∧
      ‖Real.sqrt (2 : ℝ) • D.inverse (D0 v)‖ ≤ 6 * ‖v‖ := by
  have hInv := isInvertible_of_close_identity D hD
  have hRoot0 := Real.sqrt_nonneg (2 : ℝ)
  have hRoot2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hRootLo : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith
  have hRootHi : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  obtain ⟨hLo0, hHi0⟩ := close_identity_vector_bounds D0 hD0 v
  have hHiD := (close_identity_vector_bounds D hD (D.inverse (D0 v))).2
  rw [hInv.self_apply_inverse] at hHiD
  have hLo : (1 / 3 : ℝ) * ‖v‖ ≤ ‖D.inverse (D0 v)‖ := by linarith
  have hHi : ‖D.inverse (D0 v)‖ ≤ 3 * ‖v‖ := by
    calc
      ‖D.inverse (D0 v)‖ ≤ ‖D.inverse‖ * ‖D0 v‖ := D.inverse.le_opNorm _
      _ ≤ 2 * ‖D0 v‖ := mul_le_mul_of_nonneg_right
        (norm_actual_inverse_of_close_identity D hD) (norm_nonneg _)
      _ ≤ 3 * ‖v‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hRoot0]
  constructor
  · exact hLo.trans (le_mul_of_one_le_left (norm_nonneg _) hRootLo)
  · calc
      Real.sqrt (2 : ℝ) * ‖D.inverse (D0 v)‖ ≤ 2 * ‖D.inverse (D0 v)‖ :=
        mul_le_mul_of_nonneg_right hRootHi (norm_nonneg _)
      _ ≤ 6 * ‖v‖ := by linarith

end Yau.Blueprint.C02Proof
