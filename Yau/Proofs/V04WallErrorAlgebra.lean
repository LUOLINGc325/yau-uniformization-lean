import Yau.Blueprint.VariationContracts

/-! Finite matrix identities and bounds for the actual symplectic Hessian
polynomial. These statements make no choice of local cotangent coordinates. -/

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau

variable {n : ℕ}

theorem symplecticP_add_expansion (W K : CotangentMatrix n) :
    symplecticP (W + K) - symplecticP W =
      (Matrix.trace (W.toBlocks₁₁ * K.toBlocks₂₂ᵀ +
        K.toBlocks₁₁ * W.toBlocks₂₂ᵀ + K.toBlocks₁₁ * K.toBlocks₂₂ᵀ) -
        ∑ i, ∑ j, (W.toBlocks₁₂ i j * star (K.toBlocks₁₂ j i) +
          K.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i) +
          K.toBlocks₁₂ i j * star (K.toBlocks₁₂ j i))).re := by
  have h11 : (W + K).toBlocks₁₁ = W.toBlocks₁₁ + K.toBlocks₁₁ := rfl
  have h12 : (W + K).toBlocks₁₂ = W.toBlocks₁₂ + K.toBlocks₁₂ := rfl
  have h22 : (W + K).toBlocks₂₂ = W.toBlocks₂₂ + K.toBlocks₂₂ := rfl
  simp only [symplecticP, h11, h12, h22, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, Matrix.add_apply, star_add, add_mul, mul_add,
    Finset.sum_add_distrib, Complex.sub_re, Complex.add_re]
  ring

/-- Adding a horizontal Hessian changes `p` by its contraction with the
vertical block; the mixed block is unaffected. -/
theorem symplecticP_add_horizontal (W : CotangentMatrix n)
    (L : Matrix (Fin n) (Fin n) ℂ) :
    symplecticP (W + Matrix.fromBlocks L 0 0 0) =
      symplecticP W + (Matrix.trace (L * W.toBlocks₂₂ᵀ)).re := by
  have heq := symplecticP_add_expansion W (Matrix.fromBlocks L 0 0 0)
  simp at heq
  linarith

end Yau.Blueprint.V04Proof.WallErrorAux
