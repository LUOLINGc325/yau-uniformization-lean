import Yau.Blueprint.DiscFrames
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The target's genuine Frobenius square and its invariance under a
rectangular matrix with orthonormal columns, using complex transposes. -/

open scoped Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem matrixFrobSq_eq_trace (A : Matrix κ ι ℂ) :
    matrixFrobSq A = (Matrix.trace (Aᴴ * A)).re := by
  simp only [matrixFrobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  change (∑ i, ∑ j, ‖A i j‖ ^ 2) = Complex.reCLM (∑ i, ∑ j, star (A j i) * A j i)
  simp only [map_sum, Complex.reCLM_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re]

theorem matrixFrobSq_eq_flatten_norm_sq (A : Matrix κ ι ℂ) :
    matrixFrobSq A = ‖(WithLp.toLp 2 (fun p : κ × ι => A p.1 p.2) :
      EuclideanSpace ℂ (κ × ι))‖ ^ 2 := by
  simp only [matrixFrobSq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type]

theorem matrixFrobSq_rectangular_isometry [DecidableEq ι]
    (U : Matrix κ ι ℂ) (hU : Uᴴ * U = 1) (B : Matrix ι ι ℂ) :
    matrixFrobSq (U * B * Uᵀ) = matrixFrobSq B := by
  have hUT : Uᵀ * (Uᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose] using
      congrArg Matrix.transpose hU
  have hM : (U * B * Uᵀ)ᴴ * (U * B * Uᵀ) =
      (Uᵀ)ᴴ * Bᴴ * (Uᴴ * U) * B * Uᵀ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [matrixFrobSq_eq_trace, matrixFrobSq_eq_trace, hM, hU, Matrix.mul_one]
  congr 1
  calc
    Matrix.trace ((Uᵀ)ᴴ * Bᴴ * B * Uᵀ) =
        Matrix.trace (Uᵀ * ((Uᵀ)ᴴ * Bᴴ * B)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Uᵀ * (Uᵀ)ᴴ) * (Bᴴ * B)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Bᴴ * B) := by rw [hUT, Matrix.one_mul]

end Yau.Blueprint.D05Proof
