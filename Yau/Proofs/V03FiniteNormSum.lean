import Yau.Proofs.V03Elementary
import Mathlib.Algebra.Order.Chebyshev

/-! Actual finite sums satisfy the square bound needed for componentwise
tensor difference estimates, including empty index spaces. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι F : Type*} [NormedAddCommGroup F]
    (s : Finset ι) (f : ι → F) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le s f
  have hs := mul_self_le_mul_self (norm_nonneg (∑ i ∈ s, f i)) hn
  have hnorm : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by nlinarith
  exact hnorm.trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))

end Yau.Blueprint.V03Proof
