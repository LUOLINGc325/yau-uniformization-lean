import Yau.Proofs.F01WeightedCovectorTriangle
import Yau.Proofs.F01PenaltyGradientAbsorption

/-! The actual gradient relation at a penalized Rayleigh contact absorbs
the Q-gradient and keeps the explicit vanishing properness penalty error. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {n : ℕ}

theorem penalty_contact_weighted_gradient (weights : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ weights i) (η ζ ξ : Fin n → ℂ)
    {a v W δ : ℝ} (ha : 0 < a) (hv : 0 ≤ v)
    (hW : Real.exp (rayleighPenalty a v) ≤ W) (hδ : 0 ≤ δ)
    (hξ : ξ = fun i => ((deriv (rayleighPenalty a) v : ℝ) : ℂ) * ζ i + (δ : ℂ) * η i) :
    2 * W⁻¹ * Real.sqrt (weightedCovectorSquare weights η) *
        Real.sqrt (weightedCovectorSquare weights ξ) +
        deriv (deriv (rayleighPenalty a)) v * weightedCovectorSquare weights ζ ≤
      8 * weightedCovectorSquare weights η +
        deriv (deriv (rayleighPenalty a)) v / 2 * weightedCovectorSquare weights ζ +
        2 * δ * W⁻¹ * weightedCovectorSquare weights η := by
  have hA := weightedCovectorSquare_nonneg weights hw η
  have hB := weightedCovectorSquare_nonneg weights hw ζ
  have hWp : 0 < W := lt_of_lt_of_le (Real.exp_pos _) hW
  have hj : 0 ≤ deriv (rayleighPenalty a) v :=
    ha.le.trans (rayleighPenalty_deriv_bounds ha.le hv).1
  have htri := weightedCovector_sqrt_add_le weights hw
    (fun i => ((deriv (rayleighPenalty a) v : ℝ) : ℂ) * ζ i) (fun i => (δ : ℂ) * η i)
  rw [← hξ, weightedCovector_sqrt_real_mul weights hw ζ hj,
    weightedCovector_sqrt_real_mul weights hw η hδ] at htri
  have hcross := mul_le_mul_of_nonneg_left htri
    (by positivity : 0 ≤ 2 * W⁻¹ * Real.sqrt (weightedCovectorSquare weights η))
  have hid : 2 * W⁻¹ * Real.sqrt (weightedCovectorSquare weights η) *
      (deriv (rayleighPenalty a) v * Real.sqrt (weightedCovectorSquare weights ζ) +
        δ * Real.sqrt (weightedCovectorSquare weights η)) =
      2 * (W⁻¹ * deriv (rayleighPenalty a) v) * Real.sqrt (weightedCovectorSquare weights η) *
        Real.sqrt (weightedCovectorSquare weights ζ) +
        2 * δ * W⁻¹ * weightedCovectorSquare weights η := by
    calc
      _ = 2 * (W⁻¹ * deriv (rayleighPenalty a) v) * Real.sqrt (weightedCovectorSquare weights η) *
          Real.sqrt (weightedCovectorSquare weights ζ) +
          2 * δ * W⁻¹ * (Real.sqrt (weightedCovectorSquare weights η)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hA]
  rw [hid] at hcross
  have hyoung := rayleighPenalty_absorbs_gradient ha hv hW hA hB
  linarith

end Yau.NodeProofs.F01Aux
