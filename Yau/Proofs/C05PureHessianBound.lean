import Yau.Proofs.C05HarnackAlgebra
import Mathlib.Algebra.Order.Chebyshev

/-! The positive weighted square bounds the actual pure complex quadratic form. -/

open scoped BigOperators

noncomputable section

namespace Yau.Proofs.C05Aux

variable {n : ℕ}

theorem weightedHessianSquare_entry_sq_le (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    (P : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖P i j‖ ^ 2 ≤ lam i * weightedHessianSquare lam P := by
  have hrow : (lam i)⁻¹ * ‖P i j‖ ^ 2 ≤ ∑ j, (lam i)⁻¹ * ‖P i j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (inv_nonneg.mpr (hlam i).le)
      (sq_nonneg ‖P i j‖))
      (Finset.mem_univ j)
  have hsum : (∑ j, (lam i)⁻¹ * ‖P i j‖ ^ 2) ≤ weightedHessianSquare lam P := by
    unfold weightedHessianSquare
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (inv_nonneg.mpr (hlam i).le) (sq_nonneg ‖P i j‖)) (Finset.mem_univ i)
  have h := mul_le_mul_of_nonneg_left (hrow.trans hsum) (hlam i).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hlam i)), one_mul] using h

theorem weightedHessianSquare_entry_norm_le (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    {L : ℝ} (hL : ∀ i, lam i ≤ L) (P : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖P i j‖ ≤ Real.sqrt (L * weightedHessianSquare lam P) := by
  have hsum := weightedHessianSquare_nonneg lam (fun i => (hlam i).le) P
  calc
    ‖P i j‖ = Real.sqrt (‖P i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt ((weightedHessianSquare_entry_sq_le lam hlam P i j).trans
      (mul_le_mul_of_nonneg_right (hL i) hsum))

set_option backward.isDefEq.respectTransparency false in
theorem pure_quadratic_le_weighted_square (lam : Fin n → ℝ) (hlam : ∀ i, 0 < lam i)
    {L : ℝ} (hL : ∀ i, lam i ≤ L) (P : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    ‖∑ i, ∑ j, P i j * v i * v j‖ ≤
      (n : ℝ) * Real.sqrt (L * weightedHessianSquare lam P) * (∑ i, ‖v i‖ ^ 2) := by
  let d := Real.sqrt (L * weightedHessianSquare lam P)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hsum : (∑ i, ‖v i‖) ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖))
  calc
    ‖∑ i, ∑ j, P i j * v i * v j‖ ≤ ∑ i, ∑ j, ‖P i j‖ * ‖v i‖ * ‖v j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun j => P i j * v i * v j)
    _ ≤ ∑ i, ∑ j, d * ‖v i‖ * ‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (weightedHessianSquare_entry_norm_le lam hlam hL P i j)
          (norm_nonneg _)) (norm_nonneg _)
    _ = (∑ i, d * ‖v i‖) * (∑ j, ‖v j‖) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = d * (∑ i, ‖v i‖) ^ 2 := by rw [← Finset.mul_sum]; ring
    _ ≤ d * ((n : ℝ) * ∑ i, ‖v i‖ ^ 2) := mul_le_mul_of_nonneg_left hsum hd
    _ = _ := by ring

end Yau.Proofs.C05Aux
