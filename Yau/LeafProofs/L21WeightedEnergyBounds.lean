import Yau.LeafProofs.L21WeightedPairBounds
import Yau.LeafProofs.L21QuantitativeEnergy

/-! Squared weighted energies of actual compact sums and bounded compact
multipliers, for an arbitrary smooth local weight. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

theorem weightedScalarEnergy_add_le (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (u v : CompactTest O) :
    weightedScalarEnergy φ ((u + v) : CompactTest O) ≤
      2 * weightedScalarEnergy φ u + 2 * weightedScalarEnergy φ v := by
  have hRight : Integrable (fun x => 2 * (‖u x‖ ^ 2 * Real.exp (-φ x)) +
      2 * (‖v x‖ ^ 2 * Real.exp (-φ x))) (Yau.lebesgueC n) :=
    ((integrable_weighted_test_norm_sq hO hφ u).const_mul 2).add
      ((integrable_weighted_test_norm_sq hO hφ v).const_mul 2)
  have hBound := integral_mono (integrable_weighted_test_norm_sq hO hφ (u + v))
    hRight (fun x => by
        change ‖u x + v x‖ ^ 2 * Real.exp (-φ x) ≤
          2 * (‖u x‖ ^ 2 * Real.exp (-φ x)) + 2 * (‖v x‖ ^ 2 * Real.exp (-φ x))
        exact (mul_le_mul_of_nonneg_right (norm_add_sq_le_two (u x) (v x))
          (Real.exp_pos _).le).trans_eq (by ring))
  rw [integral_add ((integrable_weighted_test_norm_sq hO hφ u).const_mul 2)
    ((integrable_weighted_test_norm_sq hO hφ v).const_mul 2), integral_const_mul, integral_const_mul] at hBound
  exact hBound

theorem weightedScalarEnergy_neg (φ : X n → ℝ) (u : CompactTest O) :
    weightedScalarEnergy φ ((-u) : CompactTest O) = weightedScalarEnergy φ u := by
  unfold weightedScalarEnergy
  simp only [AddSubgroup.coe_neg, Pi.neg_apply, norm_neg]

theorem weightedScalarEnergy_sub_le (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) (u v : CompactTest O) :
    weightedScalarEnergy φ ((u - v) : CompactTest O) ≤
      2 * weightedScalarEnergy φ u + 2 * weightedScalarEnergy φ v := by
  simpa only [sub_eq_add_neg, weightedScalarEnergy_neg] using weightedScalarEnergy_add_le hO hφ u (-v)

theorem weightedScalarEnergy_multiply_le (hO : IsOpen O) {φ : X n → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ O) {a : X n → ℂ} (ha : ContDiffOn ℝ ∞ a O)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ O, ‖a x‖ ≤ C) (u : CompactTest O) :
    weightedScalarEnergy φ (multiplyLocalTest hO ha u) ≤ C ^ 2 * weightedScalarEnergy φ u := by
  have hB := integral_mono (integrable_weighted_test_norm_sq hO hφ (multiplyLocalTest hO ha u))
    ((integrable_weighted_test_norm_sq hO hφ u).const_mul (C ^ 2)) (fun x => by
      change ‖a x * u x‖ ^ 2 * Real.exp (-φ x) ≤ C ^ 2 * (‖u x‖ ^ 2 * Real.exp (-φ x))
      by_cases hx : x ∈ O
      · rw [norm_mul, mul_pow]
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hb x hx)) (sq_nonneg ‖u x‖))
          (Real.exp_pos (-φ x)).le
        exact hh.trans_eq (by ring)
      · have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (u.property.2.2 hh))
        simp only [hu0, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, le_refl])
  rw [integral_const_mul] at hB
  exact hB

end Yau.LeafProofs.L21Aux
