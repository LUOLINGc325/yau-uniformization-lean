import Yau.Proofs.V01BivectorTrace
import Yau.Proofs.D05CanonicalAlgebra

/-! V01 scratch source: canonical cost and the paper's symplectic polynomial.
The factor one half is cancelled by the two canonical orientations. -/

noncomputable section
open Matrix
open scoped Matrix

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem trace_fromBlocks (A B D C : Herm n) :
    (Matrix.fromBlocks A B D C).trace = A.trace + C.trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type]

theorem trace_mul_transpose_swap (A B : Herm n) :
    (A * Bᵀ).trace = (B * Aᵀ).trace := by
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem trace_canonical_product_blocks (A B D C : Herm n) :
    let W := Matrix.fromBlocks A B D C
    (W * canonicalBivector * Wᵀ * (canonicalBivector : CotangentMatrix n)ᴴ).trace =
      (A * Cᵀ).trace + (C * Aᵀ).trace - (B * Dᵀ).trace - (D * Bᵀ).trace := by
  dsimp only
  simp only [Yau.Blueprint.D05Proof.canonicalBivector_fromBlocks,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.conjTranspose_neg,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, neg_zero,
    trace_fromBlocks, Matrix.trace_add, Matrix.trace_neg]
  ring

theorem bivectorCost_canonical (W : CotangentMatrix n) (hW : W.IsHermitian) :
    bivectorCost W canonicalBivector = symplecticP W := by
  have h21 : W.toBlocks₂₁ = W.toBlocks₁₂ᴴ := by
    ext i j
    exact (hW.apply (Sum.inr i) (Sum.inl j)).symm
  have hblock := trace_canonical_product_blocks W.toBlocks₁₁ W.toBlocks₁₂
    W.toBlocks₂₁ W.toBlocks₂₂
  rw [Matrix.fromBlocks_toBlocks] at hblock
  have hAC := trace_mul_transpose_swap W.toBlocks₁₁ W.toBlocks₂₂
  have hBD := trace_mul_transpose_swap W.toBlocks₁₂ W.toBlocks₂₁
  have hγ : (W.toBlocks₁₂ * W.toBlocks₂₁ᵀ).trace =
      ∑ i, ∑ j, W.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i) := by
    rw [h21]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply]
  have htrace : (W * canonicalBivector * Wᵀ * (canonicalBivector : CotangentMatrix n)ᴴ).trace =
      2 * ((W.toBlocks₁₁ * W.toBlocks₂₂ᵀ).trace -
        ∑ i, ∑ j, W.toBlocks₁₂ i j * star (W.toBlocks₁₂ j i)) := by
    rw [hblock, ← hAC, ← hBD, hγ]
    ring
  rw [bivectorCost_eq_trace, htrace]
  norm_num [symplecticP, Complex.mul_re] <;> ring

end Yau.Blueprint.V01Proof
