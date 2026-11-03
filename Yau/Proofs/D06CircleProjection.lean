import Yau.Proofs.D06CircleSobolevCore

/-! The strictly positive Fourier projection on the actual circle L² space,
with contraction in every Fourier Sobolev order. -/

open scoped lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleSobolev_mono {k l : ℕ} {f : CircleL2}
    (hf : CircleSobolev l f) (hkl : k ≤ l) : CircleSobolev k f := by
  apply hf.of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
  intro n
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by nlinarith [sq_nonneg (n : ℝ)]) hkl) (sq_nonneg _)

def circlePositiveFn (f : CircleL2) (n : ℤ) : ℂ := if 0 < n then circleCoeff f n else 0

theorem circlePositive_mem (f : CircleL2) : Memℓp (circlePositiveFn f) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℤ => ‖circlePositiveFn f n‖ ^ 2) := by
    apply (circleCoeff_norm_sq_summable f).of_nonneg_of_le (fun _ => sq_nonneg _)
    intro n
    by_cases hn : 0 < n
    · rw [circlePositiveFn, ite_eq_left hn]
    · rw [circlePositiveFn, ite_eq_right hn, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

def circlePositiveProjection (f : CircleL2) : CircleL2 :=
  (fourierBasis (T := 2 * Real.pi)).repr.symm ⟨circlePositiveFn f, circlePositive_mem f⟩

theorem circlePositiveProjection_coeff (f : CircleL2) (n : ℤ) :
    circleCoeff (circlePositiveProjection f) n = if 0 < n then circleCoeff f n else 0 := by
  simp only [circleCoeff, circlePositiveProjection, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem circlePositiveProjection_sobolev {k : ℕ} {f : CircleL2}
    (hf : CircleSobolev k f) : CircleSobolev k (circlePositiveProjection f) := by
  apply hf.of_nonneg_of_le (fun _ => mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
  intro n
  rw [circlePositiveProjection_coeff]
  by_cases hn : 0 < n
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity

theorem circlePositiveProjection_sobolev_contraction {k : ℕ} {f : CircleL2}
    (hf : CircleSobolev k f) :
    (∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff (circlePositiveProjection f) n‖ ^ 2) ≤
      ∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff f n‖ ^ 2 := by
  apply (circlePositiveProjection_sobolev hf).tsum_le_tsum _ hf
  intro n
  rw [circlePositiveProjection_coeff]
  by_cases hn : 0 < n
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity

end Yau.NodeProofs.D06Aux
