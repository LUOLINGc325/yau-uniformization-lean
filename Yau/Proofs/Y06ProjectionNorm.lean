import Yau.Proofs.Y06DiagonalCoefficients

/-! Convert the forbidden diagonal coefficient factor into an operator norm
estimate on every incoming homogeneous polynomial. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment

variable {n m : ℕ}

theorem diagonal_projection_coeffNorm_bound (a b : Fin n → ℂ) (w : Fin n → ℝ)
    {P : PolyMap n} (hP : Homogeneous P m) {δ : ℝ} (hδ : 0 ≤ δ)
    (hfactor : ∀ i (β : Fin n →₀ ℕ), β.sum (fun _ e => e) = m →
      w i < ∑ l, (β l : ℝ) * w l →
        ‖a i‖ * (∏ l ∈ β.support, ‖b l‖ ^ β l) ≤ δ) :
    (forbiddenProjection w ((linearPolynomial (Matrix.diagonal a)).comp
      (P.comp (linearPolynomial (Matrix.diagonal b))))).coeffNorm ≤ δ * P.coeffNorm := by
  classical
  apply coeffNorm_le_of_coeff_bound
  intro i β
  rw [forbiddenProjection_coeff]
  by_cases hf : w i < ∑ l, (β l : ℝ) * w l
  · rw [ite_eq_left hf, diagonal_sandwich_norm_coeff]
    by_cases hz : (P i).coeff β = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hfactor i β (hP i β hz) hf) (norm_nonneg _)
  · rw [ite_eq_right hf, norm_zero]
    exact mul_nonneg hδ (norm_nonneg _)

end Yau.Proofs.Y06Aux
