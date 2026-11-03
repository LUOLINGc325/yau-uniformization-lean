import Yau.Proofs.F01PenaltyContactGradient

/-! The exact numerical contact estimate after the actual heat chain and
gradient relation.  The remaining error is uniform in the properness penalty. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem penalty_contact_operator_bound (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (η ζ ξ : Fin n → ℂ)
    {a v W δ τ C c B G HU HQ Lf : ℝ}
    (ha : 0 < a) (hv : 0 ≤ v) (hW : Real.exp (rayleighPenalty a v) ≤ W)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hc : 0 ≤ c)
    (hξ : ξ = fun i => ((deriv (rayleighPenalty a) v : ℝ) : ℂ) * ζ i + (δ : ℂ) * η i)
    (hHU : HU ≤ C * τ + 2 * W⁻¹ * Real.sqrt (weightedCovectorSquare weights η) *
      Real.sqrt (weightedCovectorSquare weights ξ))
    (hHQ : c * τ ≤ HQ) (hLf : Lf ≤ B * τ)
    (hgradient : weightedCovectorSquare weights η ≤ G * τ) :
    HU - deriv (rayleighPenalty a) v * HQ +
        deriv (deriv (rayleighPenalty a)) v * weightedCovectorSquare weights ζ + δ * Lf ≤
      (C - c * a + 8 * G + δ * (B + 2 * G)) * τ := by
  have hA := weightedCovectorSquare_nonneg weights hw η
  have hQnorm := weightedCovectorSquare_nonneg weights hw ζ
  have hjlow := (rayleighPenalty_deriv_bounds ha.le hv).1
  have hj0 : 0 ≤ deriv (rayleighPenalty a) v := ha.le.trans hjlow
  have hjHQ : a * (c * τ) ≤ deriv (rayleighPenalty a) v * HQ :=
    (mul_le_mul_of_nonneg_right hjlow (mul_nonneg hc hτ)).trans
      (mul_le_mul_of_nonneg_left hHQ hj0)
  have hcross := penalty_contact_weighted_gradient weights hw η ζ ξ ha hv hW hδ hξ
  have hden : 0 < 1 + a * v := by positivity
  have hjsecond : deriv (deriv (rayleighPenalty a)) v ≤ 0 := by
    rw [rayleighPenalty_second_deriv a v hden.ne']
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg a)) (sq_nonneg _)
  have hnegative : deriv (deriv (rayleighPenalty a)) v / 2 *
      weightedCovectorSquare weights ζ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hjsecond (by norm_num)) hQnorm
  have hWone : 1 ≤ W :=
    (Real.one_le_exp (rayleighPenalty_nonneg ha.le hv)).trans hW
  have hinv := inv_le_one_of_one_le₀ hWone
  have hδgrad : 2 * δ * W⁻¹ * weightedCovectorSquare weights η ≤
      2 * δ * weightedCovectorSquare weights η := by
    have hh := mul_le_mul_of_nonneg_left hinv
      (by positivity : 0 ≤ 2 * δ * weightedCovectorSquare weights η)
    nlinarith
  have hgrad := mul_le_mul_of_nonneg_left hgradient (by positivity : 0 ≤ 8 + 2 * δ)
  have hf := mul_le_mul_of_nonneg_left hLf hδ
  nlinarith

end Yau.NodeProofs.F01Aux
