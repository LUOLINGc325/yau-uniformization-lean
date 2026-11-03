import Yau.Proofs.F04AuxiliaryMatrix

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic

theorem quadratic_elliptic_perturbation {n : ℕ} (A B : Mat n) (lam upper : ℝ)
    (hlam : 0 < lam) (hupper : lam ≤ upper)
    (hB : ∀ v : RIdx n → ℝ,
      lam * (∑ i, (v i) ^ 2) ≤ ∑ i, ∑ j, B i j * v i * v j ∧
      (∑ i, ∑ j, B i j * v i * v j) ≤ upper * (∑ i, (v i) ^ 2))
    (hd : ‖A - B‖ ≤ lam / 2) :
    ∀ v : RIdx n → ℝ,
      (lam / 2) * (∑ i, (v i) ^ 2) ≤ ∑ i, ∑ j, A i j * v i * v j ∧
      (∑ i, ∑ j, A i j * v i * v j) ≤ (2 * upper) * (∑ i, (v i) ^ 2) := by
  intro v
  have hQ : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hdiff := (quadratic_difference_le_frobenius A B v).trans
    (mul_le_mul_of_nonneg_right hd hQ)
  have habs := abs_le.mp hdiff
  have hBv := hB v
  have hlu := mul_le_mul_of_nonneg_right hupper hQ
  have hlQ := mul_nonneg hlam.le hQ
  constructor <;> nlinarith

theorem auxiliary_radius_bound {lam L t : ℝ} (hlam : 0 < lam) (hL : 0 ≤ L)
    (ht : -(lam / (2 * (1 + L))) < t) :
    L * (-t) ≤ lam / 2 := by
  have hden : 0 < 2 * (1 + L) := by positivity
  have htime : -t ≤ lam / (2 * (1 + L)) := by linarith
  have hscale : L * (lam / (2 * (1 + L))) ≤ lam / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  exact (mul_le_mul_of_nonneg_left htime hL).trans hscale

end Yau.F04Proof
