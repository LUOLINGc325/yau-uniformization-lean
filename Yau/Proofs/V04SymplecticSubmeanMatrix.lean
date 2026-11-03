import Yau.Proofs.D05FrobeniusAlgebra
import Yau.Blueprint.VariationContracts

open scoped Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.SymplecticSubmeanAux
open Yau Yau.Blueprint

variable {n : ℕ}

/-- The frozen antisymmetric-tensor cost is half the indicated trace.
No skewness assumption or nonempty index is needed for this algebra. -/
theorem bivectorCost_eq_half_trace (A J : CotangentMatrix n) :
    bivectorCost A J = (1 / 2 : ℝ) * (Matrix.trace (Jᴴ * A * J * Aᵀ)).re := by
  unfold bivectorCost
  congr 1
  apply congrArg Complex.re
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Exact one-half normalization for the SAME H and frame bivector.
It holds in dimension zero without taking a logarithm of zero. -/
theorem bivectorCost_gram_eq_half_frobSq (H J : CotangentMatrix n) :
    bivectorCost (Hᴴ * H) J = (1 / 2 : ℝ) * matrixFrobSq (H * J * Hᵀ) := by
  have htrace : Matrix.trace ((H * J * Hᵀ)ᴴ * (H * J * Hᵀ)) =
      Matrix.trace (Jᴴ * (Hᴴ * H) * J * (Hᴴ * H)ᵀ) := by
    calc
      Matrix.trace ((H * J * Hᵀ)ᴴ * (H * J * Hᵀ)) =
          Matrix.trace ((Hᵀ)ᴴ * (Jᴴ * (Hᴴ * H) * J * Hᵀ)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Matrix.trace ((Jᴴ * (Hᴴ * H) * J * Hᵀ) * (Hᵀ)ᴴ) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Jᴴ * (Hᴴ * H) * J * (Hᴴ * H)ᵀ) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_conjTranspose,
          Matrix.conjTranspose_transpose, Matrix.mul_assoc]
  rw [bivectorCost_eq_half_trace, D05Proof.matrixFrobSq_eq_trace, htrace]

end Yau.Blueprint.V04Proof.SymplecticSubmeanAux
