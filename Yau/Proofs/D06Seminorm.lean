import Yau.Proofs.D06NormEstimates

/-! Order estimates for the exact two-variable ENNReal boundary seminorm.
The estimates do not introduce regularity assumptions on the integrands. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

open Yau.Blueprint

variable {r : ℕ}

/-- A pointwise squared-difference estimate passes to the original seminorm,
with the same dimension-independent constant. -/
theorem halfSobolevSq_le_of_difference_le
    (a b : ℝ → Matrix (Fin r) (Fin r) ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hab : ∀ t θ, frobSq (a (t + θ) - a t) ≤ C * frobSq (b (t + θ) - b t)) :
    halfSobolevSq a ≤ ENNReal.ofReal C * halfSobolevSq b := by
  unfold halfSobolevSq
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
        ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi), ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          ENNReal.ofReal C * ENNReal.ofReal
            (frobSq (b (t + θ) - b t) / ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2) := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro θ
      dsimp only
      rw [← ENNReal.ofReal_mul hC, ← mul_div_assoc]
      exact ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hab t θ) (sq_nonneg _))
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      ac_rfl

end Yau.NodeProofs.D06Aux
