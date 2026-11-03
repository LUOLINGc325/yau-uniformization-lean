import Yau.Proofs.E01Matrix

/-! Real linear functionals on Hermitian matrices as real trace pairings. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def functionalCoefficients (L : Herm n →ₗ[ℝ] ℝ) : Herm n :=
  fun i j => (L (Matrix.single i j 1) : ℂ) +
    Complex.I * (L (Complex.I • Matrix.single i j 1) : ℂ)

def hermitianFunctionalMatrix (L : Herm n →ₗ[ℝ] ℝ) : Herm n :=
  (1 / 2 : ℂ) • (functionalCoefficients L + (functionalCoefficients L)ᴴ)

theorem linear_map_single_complex (L : Herm n →ₗ[ℝ] ℝ) (i j : Fin n) (z : ℂ) :
    L (Matrix.single i j z) =
      z.re * L (Matrix.single i j 1) +
      z.im * L (Complex.I • Matrix.single i j 1) := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  have hi : Matrix.single i j Complex.I = Complex.I • Matrix.single i j (1 : ℂ) := by
    simp [Matrix.smul_single]
  have hs : Matrix.single i j z =
      z.re • Matrix.single i j (1 : ℂ) +
        z.im • (Complex.I • Matrix.single i j (1 : ℂ)) := by
    calc
      Matrix.single i j z = Matrix.single i j (z.re • (1 : ℂ) + z.im • Complex.I) :=
        congrArg (Matrix.single i j) hz
      _ = Matrix.single i j (z.re • (1 : ℂ)) +
          Matrix.single i j (z.im • Complex.I) := Matrix.single_add _ _ _ _
      _ = _ := by
        rw [← Matrix.smul_single z.re i j (1 : ℂ),
          ← Matrix.smul_single z.im i j Complex.I, hi]
  rw [hs, map_add, map_smul, map_smul]
  rfl

theorem trace_functionalCoefficients (L : Herm n →ₗ[ℝ] ℝ) (A : Herm n) :
    (Matrix.trace ((functionalCoefficients L)ᴴ * A)).re = L A := by
  have hsum : L A = ∑ i, ∑ j,
      ((A i j).re * L (Matrix.single i j 1) +
        (A i j).im * L (Complex.I • Matrix.single i j 1)) := by
    calc
      L A = L (∑ i, ∑ j, Matrix.single i j (A i j)) :=
        congrArg L (Matrix.sum_sum_single A).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact linear_map_single_complex L i j (A i j)
  rw [hsum]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [functionalCoefficients, Complex.mul_re] <;> ring

theorem hermitianFunctionalMatrix_isHermitian (L : Herm n →ₗ[ℝ] ℝ) :
    (hermitianFunctionalMatrix L).IsHermitian := by
  unfold hermitianFunctionalMatrix Matrix.IsHermitian
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, add_comm]

theorem hermitian_trace_symmetrize (C A : Herm n) (hA : A.IsHermitian) :
    (Matrix.trace (C * A)).re = (Matrix.trace (Cᴴ * A)).re := by
  calc
    (Matrix.trace (C * A)).re = (Matrix.trace (A * C)).re := by
      rw [Matrix.trace_mul_comm]
    _ = (Matrix.trace ((Cᴴ * A)ᴴ)).re := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq]
    _ = (Matrix.trace (Cᴴ * A)).re := by
      simp only [Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]

theorem trace_hermitianFunctionalMatrix (L : Herm n →ₗ[ℝ] ℝ)
    (A : Herm n) (hA : A.IsHermitian) :
    (Matrix.trace (hermitianFunctionalMatrix L * A)).re = L A := by
  have hs := hermitian_trace_symmetrize (functionalCoefficients L) A hA
  unfold hermitianFunctionalMatrix
  rw [Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add]
  simp only [smul_eq_mul, Complex.mul_re, Complex.add_re]
  norm_num
  rw [hs, trace_functionalCoefficients]
  ring

theorem quadratic_hermitianFunctionalMatrix (L : Herm n →ₗ[ℝ] ℝ)
    (η : ComplexVector n) :
    ellipsoidQuadratic (hermitianFunctionalMatrix L) η = L (contactRankOne η) := by
  rw [← trace_mul_contactRankOne]
  exact trace_hermitianFunctionalMatrix L _ (contactRankOne_posSemidef η).isHermitian

end Yau.NodeProofs.E01Aux
