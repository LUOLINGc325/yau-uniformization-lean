import Yau.Proofs.E01LeviAlgebra

/-! Square completion for the actual inverse-transpose mixed derivative. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem adjoint_pairing_re (P : Herm n) (u ξ : ComplexVector n) :
    (star (WithLp.ofLp ξ) ⬝ᵥ (Pᴴ *ᵥ WithLp.ofLp u)).re =
      (star (WithLp.ofLp u) ⬝ᵥ (P *ᵥ WithLp.ofLp ξ)).re := by
  have heq : star (star (WithLp.ofLp u) ⬝ᵥ (P *ᵥ WithLp.ofLp ξ)) =
      star (WithLp.ofLp ξ) ⬝ᵥ (Pᴴ *ᵥ WithLp.ofLp u) := by
    rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simpa only [Complex.star_def, Complex.conj_re] using (congrArg Complex.re heq).symm

theorem inverse_levi_cross_adjoint (K A : Herm n) (hK : K.IsHermitian) :
    (K * Aᵀ * K)ᴴ = K * (Aᴴ)ᵀ * K := by
  simp only [Matrix.conjTranspose_mul, hK.eq]
  have ht : (Aᵀ)ᴴ = (Aᴴ)ᵀ := rfl
  rw [ht, Matrix.mul_assoc]

theorem inverse_levi_square_completion (K A B : Herm n) (hK : K.IsHermitian)
    (u ξ : ComplexVector n) :
    ellipsoidQuadratic K u +
      (star (WithLp.ofLp u) ⬝ᵥ ((-(K * Aᵀ * K)) *ᵥ WithLp.ofLp ξ)).re +
      (star (WithLp.ofLp ξ) ⬝ᵥ ((-(K * (Aᴴ)ᵀ * K)) *ᵥ WithLp.ofLp u)).re +
      ellipsoidQuadratic
        (K * (Aᴴ)ᵀ * K * Aᵀ * K + K * Aᵀ * K * (Aᴴ)ᵀ * K - K * Bᵀ * K) ξ =
      ellipsoidQuadratic K (u - matrixFiberMap (Aᵀ * K) ξ) +
        ellipsoidQuadratic (K * (Aᵀ * K * (Aᴴ)ᵀ - Bᵀ) * K) ξ := by
  have hcross : (star (WithLp.ofLp ξ) ⬝ᵥ ((K * (Aᴴ)ᵀ * K) *ᵥ WithLp.ofLp u)).re =
      (star (WithLp.ofLp u) ⬝ᵥ ((K * Aᵀ * K) *ᵥ WithLp.ofLp ξ)).re := by
    rw [← inverse_levi_cross_adjoint K A hK]
    exact adjoint_pairing_re _ u ξ
  have hmatrix : K * (Aᴴ)ᵀ * K * Aᵀ * K + K * Aᵀ * K * (Aᴴ)ᵀ * K - K * Bᵀ * K =
      (Aᵀ * K)ᴴ * K * (Aᵀ * K) + K * (Aᵀ * K * (Aᴴ)ᵀ - Bᵀ) * K := by
    have hc : (Aᵀ * K)ᴴ = K * (Aᴴ)ᵀ := by
      rw [Matrix.conjTranspose_mul, hK.eq]
      rfl
    rw [hc]
    noncomm_ring
  have hmap : K *ᵥ WithLp.ofLp (matrixFiberMap (Aᵀ * K) ξ) =
      (K * Aᵀ * K) *ᵥ WithLp.ofLp ξ := by
    rw [ofLp_matrixFiberMap, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hmain := dual_levi_square_completion K (Aᵀ * K)
    (K * (Aᵀ * K * (Aᴴ)ᵀ - Bᵀ) * K) hK u ξ
  rw [hmap] at hmain
  simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
  rw [hcross, hmatrix]
  linear_combination hmain

end Yau.NodeProofs.E01Aux
