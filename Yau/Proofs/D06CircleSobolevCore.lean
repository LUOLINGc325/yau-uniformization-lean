import Yau.Proofs.D06HardyPairSobolev

/-! Actual Fourier Sobolev orders and angular weak derivatives on the circle.
All coefficients are the fixed Fourier Hilbert-basis coordinates. -/

open scoped lp ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

abbrev CircleL2 := Lp ℂ 2 hardyCircleMeasure

def circleCoeff (f : CircleL2) : lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := 2 * Real.pi)).repr f

def CircleSobolev (k : ℕ) (f : CircleL2) : Prop :=
  Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff f n‖ ^ 2)

def CircleWeakDerivative (f g : CircleL2) : Prop :=
  ∀ n : ℤ, circleCoeff g n = (Complex.I * (n : ℂ)) * circleCoeff f n

theorem circleCoeff_eq_fourierCoeff (f : CircleL2) (n : ℤ) :
    circleCoeff f n = fourierCoeff f n := fourierBasis_repr f n

theorem circleCoeff_norm_sq_summable (f : CircleL2) :
    Summable (fun n : ℤ => ‖circleCoeff f n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp (circleCoeff f)).summable (by norm_num : 0 < (2 : ENNReal).toReal)

theorem circleSobolev_zero (f : CircleL2) : CircleSobolev 0 f := by
  simpa only [CircleSobolev, pow_zero, one_mul] using circleCoeff_norm_sq_summable f

theorem circleWeakDerivative_unique {f g h : CircleL2}
    (hg : CircleWeakDerivative f g) (hh : CircleWeakDerivative f h) : g = h := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  ext n
  exact (hg n).trans (hh n).symm

theorem circleDerivative_coeff_norm (c : ℂ) (n : ℤ) :
    ‖(Complex.I * (n : ℂ)) * c‖ ^ 2 = (n : ℝ) ^ 2 * ‖c‖ ^ 2 := by
  simp only [norm_mul, Complex.norm_I, one_mul, mul_pow, Complex.norm_intCast,
    Int.norm_eq_abs, sq_abs]

def circleDerivativeFn (f : CircleL2) (n : ℤ) : ℂ :=
  (Complex.I * (n : ℂ)) * circleCoeff f n

theorem circleDerivative_mem (f : CircleL2) (hf : CircleSobolev 1 f) :
    Memℓp (circleDerivativeFn f) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℤ => (n : ℝ) ^ 2 * ‖circleCoeff f n‖ ^ 2) := by
    apply hf.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro n
    simp only [pow_one]
    nlinarith [sq_nonneg ‖circleCoeff f n‖]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, circleDerivativeFn,
    circleDerivative_coeff_norm] using hs

def circleDerivative (f : CircleL2) (hf : CircleSobolev 1 f) : CircleL2 :=
  (fourierBasis (T := 2 * Real.pi)).repr.symm ⟨circleDerivativeFn f, circleDerivative_mem f hf⟩

theorem circleDerivative_weak (f : CircleL2) (hf : CircleSobolev 1 f) :
    CircleWeakDerivative f (circleDerivative f hf) := by
  intro n
  simp only [circleCoeff, circleDerivative, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem circleSobolev_succ_of_derivative (k : ℕ) {f g : CircleL2}
    (hD : CircleWeakDerivative f g) (hf : CircleSobolev k f) (hg : CircleSobolev k g) :
    CircleSobolev (k + 1) f := by
  have heq : (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (k + 1) * ‖circleCoeff f n‖ ^ 2) =
      (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff f n‖ ^ 2 +
        (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff g n‖ ^ 2) := by
    funext n
    rw [hD n, circleDerivative_coeff_norm, pow_succ]
    ring
  unfold CircleSobolev
  rw [heq]
  exact hf.add hg

end Yau.NodeProofs.D06Aux
