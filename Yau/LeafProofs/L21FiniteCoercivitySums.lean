import Mathlib

/-! Exact finite multiplicities for the derivative and zero-order Young
remainders in the corrected weighted identity. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

theorem finite_coercivity_bad_sum (n : ℕ) (E : Fin n → ℝ) (G : Fin n → Fin n → ℝ)
    (t Y Z R : ℝ) :
    (∑ i, ∑ j, ((∑ k, (t * G k j + Y * E i + t * G k i + Y * E j + E j + Z * E i)) +
      (E j + R * E i))) =
      2 * (n : ℝ) * t * (∑ i, ∑ j, G i j) +
        (2 * (n : ℝ) ^ 2 * Y + (n : ℝ) ^ 2 * (1 + Z) + (n : ℝ) * (1 + R)) * ∑ i, E i := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm (f := fun i j => G j i)]
  ring

end Yau.LeafProofs.L21Aux
