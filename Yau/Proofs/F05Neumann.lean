import Mathlib

/-! The correction is an operator-norm convergent series on the actual Banach space. -/

noncomputable section

namespace Yau.Proofs.F05Aux

theorem neumann_inverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (R : E →L[ℝ] E) (hR : ‖R‖ ≤ (1/4 : ℝ)) :
    ∃ N : E →L[ℝ] E,
      (ContinuousLinearMap.id ℝ E + R).comp N = ContinuousLinearMap.id ℝ E ∧
      N.comp (ContinuousLinearMap.id ℝ E + R) = ContinuousLinearMap.id ℝ E ∧
      ‖N‖ ≤ 2 := by
  have hn : ‖-R‖ ≤ (1/4 : ℝ) := by simpa only [norm_neg] using hR
  have hn1 : ‖-R‖ < 1 := by linarith
  let N : E →L[ℝ] E := ∑' k : ℕ, (-R)^k
  refine ⟨N, ?_, ?_, ?_⟩
  · change (1 + R) * N = 1
    simpa only [sub_neg_eq_add] using mul_neg_geom_series (-R) hn1
  · change N * (1 + R) = 1
    simpa only [sub_neg_eq_add] using geom_series_mul_neg (-R) hn1
  · have hb := tsum_geometric_le_of_norm_lt_one (-R) hn1
    have hone : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hden : 0 < 1 - ‖-R‖ := by linarith
    have hmul : (1 - ‖-R‖) * (1 - ‖-R‖)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
    have hinv : 0 ≤ (1 - ‖-R‖)⁻¹ := inv_nonneg.mpr hden.le
    change ‖∑' k : ℕ, (-R)^k‖ ≤ 2
    nlinarith

end Yau.Proofs.F05Aux
