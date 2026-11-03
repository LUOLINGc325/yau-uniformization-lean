import Yau.Proofs.C02OperatorInverse

/-! Uniform comparison in the actual coordinate tangent space. These estimates
will be applied to the endpoint Jacobi differential in a parallel frame. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem close_identity_vector_bounds
    (B : E →L[ℝ] E) (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ≤ ‖B v‖ ∧ ‖B v‖ ≤ (3 / 2 : ℝ) * ‖v‖ := by
  have hd : ‖B v - v‖ ≤ (1 / 4 : ℝ) * ‖v‖ := by
    calc
      ‖B v - v‖ = ‖(B - ContinuousLinearMap.id ℝ E) v‖ := rfl
      _ ≤ ‖B - ContinuousLinearMap.id ℝ E‖ * ‖v‖ :=
        (B - ContinuousLinearMap.id ℝ E).le_opNorm v
      _ ≤ (1 / 4 : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg v)
  have hu : ‖B v‖ ≤ ‖B v - v‖ + ‖v‖ := by
    simpa only [sub_add_cancel] using norm_add_le (B v - v) v
  have hl : ‖v‖ ≤ ‖B v - v‖ + ‖B v‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using norm_add_le (v - B v) (B v)
  constructor <;> nlinarith [norm_nonneg v]

theorem close_identity_squared_bounds
    (B : E →L[ℝ] E) (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) (v : E) :
    (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖B v‖ ^ 2 ∧
      ‖B v‖ ^ 2 ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
  obtain ⟨hl, hu⟩ := close_identity_vector_bounds B hB v
  have hll := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ (1 / 2) * ‖v‖) hl
  have huu := mul_self_le_mul_self (norm_nonneg (B v)) hu
  constructor <;> nlinarith

end Yau.Blueprint.C02Proof
