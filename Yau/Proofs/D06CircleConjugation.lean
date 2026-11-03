import Yau.Proofs.D06CircleSobolevAlgebra

/-! Conjugation and the strictly positive Fourier recovery used for the fixed
source-defined B=h′p in the original Sobolev bootstrap. -/

open scoped ComplexConjugate

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circleCoeff_star (f : CircleL2) (n : ℤ) :
    circleCoeff (star f) n = conj (circleCoeff f (-n)) := by
  rw [circleCoeff_eq_fourierCoeff]
  have h := congrFun (fourierCoeff_congr_ae (MeasureTheory.Lp.coeFn_star f)) n
  rw [h]
  change fourierCoeff (fun t => conj (f t)) n = _
  rw [hardy_fourierCoeff_conj, circleCoeff_eq_fourierCoeff]

theorem circleSobolev_star {k : ℕ} {f : CircleL2} (hf : CircleSobolev k f) :
    CircleSobolev k (star f) := by
  let W : ℤ → ℝ := fun n => (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff f n‖ ^ 2
  have hW : Summable W := hf
  have h := hW.comp_injective (neg_injective : Function.Injective (fun n : ℤ => -n))
  apply h.congr
  intro n
  change (1 + ((-n : ℤ) : ℝ) ^ 2) ^ k * ‖circleCoeff f (-n)‖ ^ 2 =
    (1 + (n : ℝ) ^ 2) ^ k * ‖circleCoeff (star f) n‖ ^ 2
  rw [circleCoeff_star]
  simp only [Int.cast_neg, neg_sq, Complex.norm_conj]

theorem circleWeakDerivative_star {f df : CircleL2} (hD : CircleWeakDerivative f df) :
    CircleWeakDerivative (star f) (star df) := by
  intro n
  rw [circleCoeff_star, circleCoeff_star, hD (-n)]
  simp only [map_mul, map_neg, map_intCast, Complex.conj_I, Int.cast_neg]
  ring

theorem circlePositiveProjection_recover (B C : CircleL2)
    (hpos : ∀ n : ℤ, n ≤ 0 → circleCoeff B n = 0) (hC : C = B + star B) :
    circlePositiveProjection C = B := by
  apply (fourierBasis (T := 2 * Real.pi)).repr.injective
  ext n
  change circleCoeff (circlePositiveProjection C) n = circleCoeff B n
  rw [circlePositiveProjection_coeff, hC, circleCoeff_add, circleCoeff_star]
  by_cases hn : 0 < n
  · rw [ite_eq_left hn, hpos (-n) (by omega), map_zero, add_zero]
  · rw [ite_eq_right hn, hpos n (by omega)]

end Yau.NodeProofs.D06Aux
