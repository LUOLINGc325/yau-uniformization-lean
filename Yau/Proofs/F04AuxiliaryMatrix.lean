import spec.CHAIN.ParabolicCandidates

/-! Quantitative matrix algebra for the exact auxiliary coefficient
extension target, with its original Frobenius norm convention. -/

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic

theorem frobenius_norm_sq {n : ℕ} (A : Mat n) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg (A i j))))

theorem quadratic_le_frobenius {n : ℕ} (D : Mat n) (v : RIdx n → ℝ) :
    |∑ i, ∑ j, D i j * v i * v j| ≤ ‖D‖ * (∑ i, (v i) ^ 2) := by
  have hc : (∑ i, ∑ j, D i j * (v i * v j)) ^ 2 ≤
      (∑ i, ∑ j, (D i j) ^ 2) * ∑ i, ∑ j, (v i * v j) ^ 2 := by
    simpa only [Fintype.sum_prod_type] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (RIdx n × RIdx n))
        (fun p => D p.1 p.2) (fun p => v p.1 * v p.2)
  have hout : (∑ i, ∑ j, (v i * v j) ^ 2) = (∑ i, (v i) ^ 2) ^ 2 := by
    calc
      _ = ∑ i, ∑ j, (v i) ^ 2 * (v j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i, (v i) ^ 2) * ∑ j, (v j) ^ 2 := (Fintype.sum_mul_sum _ _).symm
      _ = _ := (pow_two _).symm
  rw [hout, ← frobenius_norm_sq D] at hc
  have hQ : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hD : 0 ≤ ‖D‖ := norm_nonneg D
  have hprod : 0 ≤ ‖D‖ * (∑ i, (v i) ^ 2) := mul_nonneg hD hQ
  have heq : (∑ i, ∑ j, D i j * (v i * v j)) = ∑ i, ∑ j, D i j * v i * v j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hc
  nlinarith [sq_abs (∑ i, ∑ j, D i j * v i * v j)]

theorem quadratic_difference_le_frobenius {n : ℕ} (A B : Mat n) (v : RIdx n → ℝ) :
    |(∑ i, ∑ j, A i j * v i * v j) - (∑ i, ∑ j, B i j * v i * v j)| ≤
      ‖A - B‖ * (∑ i, (v i) ^ 2) := by
  convert quadratic_le_frobenius (A - B) v using 1
  simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem symmetricPart_difference_le {n : ℕ} (A B : Mat n) (hB : B.IsSymm) :
    ‖(1 / 2 : ℝ) • (A + Aᵀ) - B‖ ≤ ‖A - B‖ := by
  have heq : (1 / 2 : ℝ) • (A + Aᵀ) - B =
      (1 / 2 : ℝ) • ((A - B) + (A - B)ᵀ) := by
    ext i j
    have hBij := hB.apply i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul] at *
    linarith
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖(A - B) + (A - B)ᵀ‖ ≤
        (1 / 2 : ℝ) * (‖A - B‖ + ‖(A - B)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A - B‖ := by rw [Matrix.frobenius_norm_transpose]; ring

end Yau.F04Proof
