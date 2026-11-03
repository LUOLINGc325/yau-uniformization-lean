import Yau.Proofs.Y03Triangular

/-! The actual nonsingular inverse is a fixed finite polynomial under strict weight support. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem strict_weight_inverse_polynomial (L : Herm n) (w : Fin n → ℝ)
    (hdiag : ∀ i, L i i = 1)
    (hsupport : ∀ i j, i ≠ j → L i j ≠ 0 → w i < w j) :
    L⁻¹ = ∑ r ∈ Finset.range n, (-(L - 1)) ^ r := by
  have hnil := strict_weight_difference_pow_eq_zero L w hdiag hsupport
  have hneg : (-(L - 1)) ^ n = 0 := by rw [neg_pow, hnil, mul_zero]
  have heq : 1 - (-(L - 1)) = L := by abel
  have hleft : (∑ r ∈ Finset.range n, (-(L - 1)) ^ r) * L = 1 := by
    have hgeom := geom_sum_mul_neg (-(L - 1)) n
    rw [heq, hneg, sub_zero] at hgeom
    exact hgeom
  exact Matrix.inv_eq_left_inv hleft

theorem strict_weight_isUnit (L : Herm n) (w : Fin n → ℝ)
    (hdiag : ∀ i, L i i = 1)
    (hsupport : ∀ i j, i ≠ j → L i j ≠ 0 → w i < w j) : IsUnit L := by
  have hnil := strict_weight_difference_pow_eq_zero L w hdiag hsupport
  have hneg : (-(L - 1)) ^ n = 0 := by rw [neg_pow, hnil, mul_zero]
  have heq : 1 - (-(L - 1)) = L := by abel
  let P := ∑ r ∈ Finset.range n, (-(L - 1)) ^ r
  have hleft : P * L = 1 := by
    have hgeom := geom_sum_mul_neg (-(L - 1)) n
    rw [heq, hneg, sub_zero] at hgeom
    exact hgeom
  have hright : L * P = 1 := by
    have hgeom := mul_neg_geom_sum (-(L - 1)) n
    rw [heq, hneg, sub_zero] at hgeom
    exact hgeom
  exact ⟨⟨L, P, hright, hleft⟩, rfl⟩

end Yau.Blueprint.Alignment.Y03Proof
