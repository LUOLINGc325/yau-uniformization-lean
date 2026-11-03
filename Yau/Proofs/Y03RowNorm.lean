import Yau.Proofs.Y03OrderedRates

/-! Euclidean norm bounds in the contract's row-covector convention. -/

open scoped Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def rowApply (A : Herm n) (v : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (WithLp.ofLp v ᵥ* A)

def conjugateVector (v : ComplexVector n) : ComplexVector n := WithLp.toLp 2 (star (WithLp.ofLp v))

theorem conjugateVector_norm (v : ComplexVector n) : ‖conjugateVector v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector, Pi.star_apply, norm_star]

theorem rowApply_conjugate (A : Herm n) (v : ComplexVector n) :
    conjugateVector (rowApply A v) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A.conjTranspose (conjugateVector v) := by
  apply WithLp.ofLp_injective
  exact Matrix.star_vecMul A (WithLp.ofLp v)

open scoped Matrix.Norms.L2Operator in
theorem matOpNorm_conjTranspose (A : Herm n) : matOpNorm A.conjTranspose = matOpNorm A := by
  exact norm_star A

theorem rowApply_norm_le (A : Herm n) (v : ComplexVector n) :
    ‖rowApply A v‖ ≤ matOpNorm A * ‖v‖ := by
  rw [← conjugateVector_norm (rowApply A v), rowApply_conjugate]
  exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A.conjTranspose).le_opNorm _).trans_eq
    (by rw [conjugateVector_norm]; change matOpNorm A.conjTranspose * ‖v‖ = _; rw [matOpNorm_conjTranspose])

theorem rowApply_norm_unitary {A : Herm n} (hA : Unitary A) (v : ComplexVector n) :
    ‖rowApply A v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp only [EuclideanSpace.norm_sq_eq]
  exact unitary_row_norm_square_sum hA (WithLp.ofLp v)

theorem rowApply_add (A : Herm n) (v w : ComplexVector n) :
    rowApply A (v + w) = rowApply A v + rowApply A w := by
  apply WithLp.ofLp_injective
  change (WithLp.ofLp v + WithLp.ofLp w) ᵥ* A = _
  exact Matrix.add_vecMul _ _ _

theorem rowApply_mul (A B : Herm n) (v : ComplexVector n) :
    rowApply (A * B) v = rowApply B (rowApply A v) := by
  apply WithLp.ofLp_injective
  change WithLp.ofLp v ᵥ* (A * B) = (WithLp.ofLp v ᵥ* A) ᵥ* B
  exact (Matrix.vecMul_vecMul _ _ _).symm

end Yau.Blueprint.Alignment.Y03Proof
