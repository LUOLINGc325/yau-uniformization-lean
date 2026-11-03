import Yau.Proofs.E01ChernTensor

/-! Exact finite quadratic contraction; the curvature vector is conjugated in the native convention. -/

noncomputable section
open scoped Matrix

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem complex_quadratic_weighted_matrix_sum
    (R : Fin n → Fin n → Herm n) (a : Fin n → ℂ) (ξ : ComplexVector n) :
    star (WithLp.ofLp ξ) ⬝ᵥ
        ((∑ k, ∑ l, (a k * star (a l)) • R k l) *ᵥ WithLp.ofLp ξ) =
      ∑ i, ∑ j, ∑ k, ∑ l, R k l i j * star (ξ i) * ξ j * a k * star (a l) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply,
    Pi.star_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem quadratic_chern_residual_contraction
    (G : Herm n) (A C : Fin n → Herm n) (M : Fin n → Fin n → Herm n)
    (a : Fin n → ℂ) (ξ : ComplexVector n) :
    ellipsoidQuadratic ((∑ k, a k • A k)ᵀ * Gᵀ * (∑ l, star (a l) • C l)ᵀ -
        (∑ k, ∑ l, (a k * star (a l)) • M k l)ᵀ) ξ =
      (∑ i, ∑ j, ∑ k, ∑ l,
        (-M k l j i + ∑ p, ∑ q, G p q * A k q i * C l j p) *
          star (ξ i) * ξ j * a k * star (a l)).re := by
  rw [chern_residual_direction_sum]
  unfold ellipsoidQuadratic
  rw [complex_quadratic_weighted_matrix_sum]
  simp only [chern_residual_entry]

end Yau.NodeProofs.E01Aux
