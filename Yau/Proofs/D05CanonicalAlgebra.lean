import Yau.Blueprint.DiscFrames
import Mathlib.Data.Matrix.Block

/-! The canonical cotangent bivector and the precise transpose convention
in the symplectic block calculation, including the empty index type. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {n : ℕ}

theorem canonicalBivector_fromBlocks : (canonicalBivector : CotangentMatrix n) =
    Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  cases i <;> cases j <;> simp [canonicalBivector, Matrix.one_apply]
  split_ifs <;> simp

theorem canonicalBivector_transpose : (canonicalBivector : CotangentMatrix n)ᵀ =
    -canonicalBivector := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [canonicalBivector]
      | inr j => by_cases hij : i = j <;> simp [canonicalBivector, hij, eq_comm]
  | inr i =>
      cases j with
      | inl j => by_cases hij : i = j <;> simp [canonicalBivector, hij, eq_comm]
      | inr j => simp [canonicalBivector]

theorem canonicalBivector_conjTranspose : (canonicalBivector : CotangentMatrix n)ᴴ =
    -canonicalBivector := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp [canonicalBivector]
      | inr j => by_cases hij : i = j <;> simp [canonicalBivector, hij, eq_comm]
  | inr i =>
      cases j with
      | inl j => by_cases hij : i = j <;> simp [canonicalBivector, hij, eq_comm]
      | inr j => simp [canonicalBivector]

theorem canonicalBivector_square :
    (canonicalBivector : CotangentMatrix n) * canonicalBivector = -1 := by
  rw [canonicalBivector_fromBlocks]
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero]
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply]

theorem canonicalBivector_gram :
    (canonicalBivector : CotangentMatrix n)ᴴ * canonicalBivector = 1 := by
  rw [canonicalBivector_conjTranspose, Matrix.neg_mul, canonicalBivector_square, neg_neg]

theorem canonicalBivector_block_symplectic (A B C : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * Bᵀ = 1) (hCB : C * Bᵀ = B * Cᵀ) :
    let T := Matrix.fromBlocks A 0 C B
    T * canonicalBivector * Tᵀ = (canonicalBivector : CotangentMatrix n) := by
  have hBA : B * Aᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
      congrArg Matrix.transpose hAB
  dsimp only
  rw [canonicalBivector_fromBlocks, Matrix.fromBlocks_transpose]
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, Matrix.transpose_zero,
    Matrix.mul_neg, Matrix.neg_mul, hAB, hBA, hCB, neg_add_cancel, neg_zero]

end Yau.Blueprint.D05Proof
