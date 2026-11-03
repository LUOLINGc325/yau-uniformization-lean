import Yau.Blueprint.Alignment

/-! A quantitative perturbation bound for the actual diagonal rate form. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem sum_norm_mul_le (v e : ComplexVector n) :
    (∑ i, ‖v i‖ * ‖e i‖) ≤ ‖v‖ * ‖e‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun i : Fin n => ‖v i‖) (fun i : Fin n => ‖e i‖)
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq] at hcs
  have hnonneg : 0 ≤ ∑ i, ‖v i‖ * ‖e i‖ := Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [mul_nonneg (norm_nonneg v) (norm_nonneg e)]

theorem diagonal_quadratic_perturbation (μ : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ B) (v e : ComplexVector n) :
    (∑ i, μ i * ‖(v + e) i‖ ^ 2) ≤ (∑ i, μ i * ‖v i‖ ^ 2) +
      B * (2 * ‖v‖ * ‖e‖ + ‖e‖ ^ 2) := by
  have hpoint (i : Fin n) : μ i * ‖(v + e) i‖ ^ 2 ≤
      μ i * ‖v i‖ ^ 2 + B * (2 * ‖v i‖ * ‖e i‖ + ‖e i‖ ^ 2) := by
    have hnorm := norm_add_le (v i) (e i)
    have hsquare : ‖v i + e i‖ ^ 2 ≤ ‖v i‖ ^ 2 + 2 * ‖v i‖ * ‖e i‖ + ‖e i‖ ^ 2 := by
      nlinarith [norm_nonneg (v i + e i), norm_nonneg (v i), norm_nonneg (e i)]
    have hmul := mul_le_mul_of_nonneg_left hsquare (hμ i).1
    have hpay := mul_le_mul_of_nonneg_right (hμ i).2
      (by positivity : 0 ≤ 2 * ‖v i‖ * ‖e i‖ + ‖e i‖ ^ 2)
    change μ i * ‖v i + e i‖ ^ 2 ≤ _
    nlinarith
  calc
    _ ≤ ∑ i, (μ i * ‖v i‖ ^ 2 + B * (2 * ‖v i‖ * ‖e i‖ + ‖e i‖ ^ 2)) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, μ i * ‖v i‖ ^ 2) + B * (2 * (∑ i, ‖v i‖ * ‖e i‖) + ‖e‖ ^ 2) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq,
        mul_assoc]
    _ ≤ _ := by
      have hcs := sum_norm_mul_le v e
      nlinarith

end Yau.Blueprint.Alignment.Y03Proof
