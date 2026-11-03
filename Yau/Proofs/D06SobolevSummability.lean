import Yau.Proofs.D06CircleSobolevCore

/-! The one-dimensional Fourier Cauchy--Schwarz estimate: one Sobolev order
makes the same actual Fourier coefficients absolutely summable. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

theorem circle_summable_inverse_weight : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by decide)
  have hd : Summable (fun n : ℤ => if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply (hd.add hp).of_nonneg_of_le (fun n => inv_nonneg.mpr (by positivity))
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [hn, ite_false, zero_add]
    have hpos : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
    simpa only [one_div] using (one_div_le_one_div_of_le hpos (by linarith))

theorem summable_coeff_of_weighted_square (a : ℤ → ℂ)
    (ha : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2)) :
    Summable (fun n : ℤ => ‖a n‖) := by
  let S := ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2
  let T := ∑' n : ℤ, (1 + (n : ℝ) ^ 2)⁻¹
  apply summable_of_sum_le (fun _ => norm_nonneg _) (c := Real.sqrt S * Real.sqrt T)
  intro F
  have heq (n : ℤ) : ‖a n‖ = Real.sqrt ((1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2) *
      Real.sqrt ((1 + (n : ℝ) ^ 2)⁻¹) := by
    have hw : 0 < 1 + (n : ℝ) ^ 2 := by positivity
    have hs : Real.sqrt (1 + (n : ℝ) ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
    rw [Real.sqrt_mul hw.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_inv]
    field_simp
  calc
    (∑ n ∈ F, ‖a n‖) = ∑ n ∈ F,
        Real.sqrt ((1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2) * Real.sqrt ((1 + (n : ℝ) ^ 2)⁻¹) :=
      Finset.sum_congr rfl (fun n _ => heq n)
    _ ≤ Real.sqrt (∑ n ∈ F, (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2) *
        Real.sqrt (∑ n ∈ F, (1 + (n : ℝ) ^ 2)⁻¹) :=
      Real.sum_sqrt_mul_sqrt_le F (fun n => by positivity) (fun n => by positivity)
    _ ≤ Real.sqrt S * Real.sqrt T := mul_le_mul
      (Real.sqrt_le_sqrt (ha.sum_le_tsum F (fun n _ => by positivity)))
      (Real.sqrt_le_sqrt (circle_summable_inverse_weight.sum_le_tsum F (fun n _ => by positivity)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem circleSobolev_one_summable_coeff {f : CircleL2} (hf : CircleSobolev 1 f) :
    Summable (fun n : ℤ => ‖circleCoeff f n‖) :=
  summable_coeff_of_weighted_square _ (by simpa only [CircleSobolev, pow_one] using hf)

end Yau.NodeProofs.D06Aux
