import Yau.Proofs.D06CircleSobolevDerivative
import Yau.Proofs.D06SobolevSummability

/-! All Fourier Sobolev orders of an original Hardy trace imply all polynomial
weighted ℓ¹ orders of those same Taylor coefficients, for actual closed-disc jets. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyEntry_weighted_summable (a : HardySeq r) (i : Fin r)
    (ha : ∀ k : ℕ, CircleSobolev k (hardyTraceLp a i)) (m : ℕ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ m * ‖a (n, i)‖) := by
  let f := hardyTraceLp a i
  let b : ℤ → ℂ := fun n => (((1 + (n : ℝ) ^ 2) ^ m : ℝ) : ℂ) * circleCoeff f n
  have hraw : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (2 * m + 1) * ‖circleCoeff f n‖ ^ 2) :=
    ha (2 * m + 1)
  have hb : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖b n‖ ^ 2) := by
    apply hraw.congr
    intro n
    change (1 + (n : ℝ) ^ 2) ^ (2 * m + 1) * ‖circleCoeff f n‖ ^ 2 =
      (1 + (n : ℝ) ^ 2) * ‖(((1 + (n : ℝ) ^ 2) ^ m : ℝ) : ℂ) * circleCoeff f n‖ ^ 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _), mul_pow]
    rw [← pow_mul, show m * 2 = 2 * m by omega, pow_succ]
    ring
  have hs := (summable_coeff_of_weighted_square b hb).comp_injective Int.ofNat_injective
  have hn : Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2) ^ m * ‖a (n, i)‖) := by
    apply hs.congr
    intro n
    change ‖(((1 + ((n : ℤ) : ℝ) ^ 2) ^ m : ℝ) : ℂ) * circleCoeff (hardyTraceLp a i) (n : ℤ)‖ = _
    rw [circleCoeff_eq_fourierCoeff, hardyTrace_fourierCoeff]
    simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast, Int.cast_natCast,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (show 0 ≤ (1 + (n : ℝ) ^ 2) ^ m by positivity)]
  apply (hn.mul_left ((2 : ℝ) ^ m)).of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hw : (n : ℝ) + 1 ≤ 2 * (1 + (n : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 1) hw m
  have h := mul_le_mul_of_nonneg_right hp (norm_nonneg (a (n, i)))
  simpa only [Nat.cast_add, Nat.cast_one, mul_pow, mul_assoc] using h

end Yau.NodeProofs.D06Aux
