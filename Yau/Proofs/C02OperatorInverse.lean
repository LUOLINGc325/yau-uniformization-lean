import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Normed.Ring.Units

/-! A computed two-sided inverse for the endpoint Jacobi operator, with a
uniform norm bound. The Banach space here is the coordinate tangent space. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_bounded_inverse_of_close_identity
    (B : E →L[ℝ] E) (hB : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 4) :
    ∃ V : E →L[ℝ] E,
      V.comp B = ContinuousLinearMap.id ℝ E ∧
      B.comp V = ContinuousLinearMap.id ℝ E ∧ ‖V‖ ≤ 2 := by
  let T : E →L[ℝ] E := 1 - B
  have hT : ‖T‖ ≤ 1 / 4 := by
    dsimp only [T]
    rw [norm_sub_rev]
    exact hB
  have hTsmall : ‖T‖ < 1 := by linarith
  let u : (E →L[ℝ] E)ˣ := Units.oneSub T hTsmall
  let V : E →L[ℝ] E := (u⁻¹ : (E →L[ℝ] E)ˣ)
  have hu : (u : E →L[ℝ] E) = B := by
    change 1 - (1 - B) = B
    abel
  have hGeom := tsum_geometric_le_of_norm_lt_one T hTsmall
  change ‖V‖ ≤ ‖(1 : E →L[ℝ] E)‖ - 1 + (1 - ‖T‖)⁻¹ at hGeom
  have hDen : 0 < 1 - ‖T‖ := by linarith
  have hInv : (1 - ‖T‖)⁻¹ ≤ 2 := by
    have hMul : (1 - ‖T‖) * (1 - ‖T‖)⁻¹ = (1 : ℝ) :=
      mul_inv_cancel₀ (ne_of_gt hDen)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - ‖T‖ by linarith)
      (le_of_lt (inv_pos.mpr hDen))]
  have hOne : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  refine ⟨V, ?_, ?_, by linarith⟩
  · change V * B = 1
    simpa only [hu] using (show V * (u : E →L[ℝ] E) = 1 from u.inv_val)
  · change B * V = 1
    simpa only [hu] using (show (u : E →L[ℝ] E) * V = 1 from u.val_inv)

end Yau.Blueprint.C02Proof
