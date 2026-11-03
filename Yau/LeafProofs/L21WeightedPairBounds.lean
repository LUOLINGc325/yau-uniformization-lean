import Yau.LeafProofs.L21UniformCorrectedLevi
import Yau.LeafProofs.L21WeakProducts

/-! Actual compact weighted pairings obey coefficient bounds and Young's
inequality, with no bound on the singular weight derivatives. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

theorem young_real_product (a b C t : ℝ) (ht : 0 < t) :
    C * a * b ≤ t * b ^ 2 + (C ^ 2 / (4 * t)) * a ^ 2 := by
  have hid : 4 * t * (t * b ^ 2 + (C ^ 2 / (4 * t)) * a ^ 2 - C * a * b) =
      (2 * t * b - C * a) ^ 2 := by
    field_simp
    ring
  have hh := sq_nonneg (2 * t * b - C * a)
  have hp : 0 < 4 * t := by positivity
  nlinarith

theorem integrable_weighted_test_norm_sq (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (u : CompactTest O) :
    Integrable (fun x => ‖u x‖ ^ 2 * Real.exp (-φ x)) (Yau.lebesgueC n) := by
  have hh := (integrable_test_pair hO hφ u u).re
  convert! hh using 1
  funext x
  change ‖u x‖ ^ 2 * Real.exp (-φ x) =
    ((star (u x) * u x) * (Real.exp (-φ x) : ℂ)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    mul_comm (star (u x)) (u x), complex_re_mul_star]

theorem weightedScalarEnergy_nonneg (φ : X n → ℝ) (u : X n → ℂ) :
    0 ≤ weightedScalarEnergy φ u :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem testPair_multiply_young (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O)
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (hb : ∀ x ∈ O, ‖a x‖ ≤ C)
    (u v : CompactTest O) :
    |testPair φ u (multiplyLocalTest hO ha v)| ≤
      t * weightedScalarEnergy φ v + (C ^ 2 / (4 * t)) * weightedScalarEnergy φ u := by
  let w := multiplyLocalTest hO ha v
  have hReal : Integrable (fun x => t * (‖v x‖ ^ 2 * Real.exp (-φ x)) +
      (C ^ 2 / (4 * t)) * (‖u x‖ ^ 2 * Real.exp (-φ x))) (Yau.lebesgueC n) :=
    ((integrable_weighted_test_norm_sq hO hφ v).const_mul t).add
      ((integrable_weighted_test_norm_sq hO hφ u).const_mul _)
  have hPoint (x : X n) : ‖star (u x) * w x * weightDensity φ x‖ ≤
      t * (‖v x‖ ^ 2 * Real.exp (-φ x)) +
        (C ^ 2 / (4 * t)) * (‖u x‖ ^ 2 * Real.exp (-φ x)) := by
    by_cases hx : x ∈ O
    · change ‖star (u x) * (a x * v x) * (Real.exp (-φ x) : ℂ)‖ ≤ _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hcoef : ‖u x‖ * (‖a x‖ * ‖v x‖) ≤ C * ‖u x‖ * ‖v x‖ := by
        calc
          _ ≤ ‖u x‖ * (C * ‖v x‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _)) (norm_nonneg _)
          _ = _ := by ring
      calc
        _ ≤ (C * ‖u x‖ * ‖v x‖) * Real.exp (-φ x) :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
        _ ≤ (t * ‖v x‖ ^ 2 + (C ^ 2 / (4 * t)) * ‖u x‖ ^ 2) * Real.exp (-φ x) :=
          mul_le_mul_of_nonneg_right (young_real_product ‖u x‖ ‖v x‖ C t ht) (Real.exp_pos _).le
        _ = _ := by ring
    · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (u.property.2.2 hh))
      have hv0 : v x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (v.property.2.2 hh))
      simp only [hu0, hv0, star_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero]
      exact le_refl 0
  have hNorm := norm_integral_le_of_norm_le hReal (Filter.Eventually.of_forall hPoint)
  have hAbs := (Complex.abs_re_le_norm _).trans hNorm
  change |(∫ x, star (u x) * w x * weightDensity φ x ∂Yau.lebesgueC n).re| ≤ _
  apply hAbs.trans_eq
  rw [integral_add ((integrable_weighted_test_norm_sq hO hφ v).const_mul t)
    ((integrable_weighted_test_norm_sq hO hφ u).const_mul _), integral_const_mul, integral_const_mul]
  rfl

theorem testPair_multiply_lower (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O)
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) (hb : ∀ x ∈ O, ‖a x‖ ≤ C)
    (u v : CompactTest O) :
    -(t * weightedScalarEnergy φ v + (C ^ 2 / (4 * t)) * weightedScalarEnergy φ u) ≤
      testPair φ u (multiplyLocalTest hO ha v) :=
  (abs_le.mp (testPair_multiply_young hO hφ ha hC ht hb u v)).1

end Yau.LeafProofs.L21Aux
