import Yau.Proofs.V04FactorTransport

/-! Scalar Lipschitz calculus is Lipschitz for the Frobenius norm, proved
by comparing two fixed eigenbases. No operator-norm Lipschitz assertion is
used. Empty matrix index types remain covered by the finite sums. -/

open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem matrixFrobSq_unitary_left_right (A U V : CotangentMatrix n)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) : matrixFrobSq (Uᴴ * A * V) = matrixFrobSq A := by
  have hv : matrixFrobSq (Uᴴ * A * V) = matrixFrobSq (Uᴴ * A) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      matrixFrobSq_mul_unitaryAdj (Uᴴ * A) Vᴴ (by simpa using hV)
  rw [hv, ← cotangentMatrixHS_norm_sq, cotangentMatrixHS_norm_sq_trace,
    ← cotangentMatrixHS_norm_sq, cotangentMatrixHS_norm_sq_trace]
  calc
    _ = (Matrix.trace (Aᴴ * (U * Uᴴ) * A)).re := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [hU]; simp

theorem spectral_difference_sandwich_entry (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (g : ℝ → ℝ) (i j : CotangentIndex n) :
    (((hA.eigenvectorUnitary : CotangentMatrix n)ᴴ *
      (hermitianScalar g A - hermitianScalar g B) * (hB.eigenvectorUnitary : CotangentMatrix n)) i j) =
      (((g (hA.eigenvalues i) : ℝ) : ℂ) - ((g (hB.eigenvalues j) : ℝ) : ℂ)) *
        (((hA.eigenvectorUnitary : CotangentMatrix n)ᴴ *
          (hB.eigenvectorUnitary : CotangentMatrix n)) i j) := by
  let U : CotangentMatrix n := hA.eigenvectorUnitary
  let V : CotangentMatrix n := hB.eigenvectorUnitary
  let D : CotangentMatrix n := Matrix.diagonal (fun i => (g (hA.eigenvalues i) : ℂ))
  let E : CotangentMatrix n := Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ))
  have hu : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hv : Vᴴ * V = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have heq : Uᴴ * (U * D * Uᴴ - V * E * Vᴴ) * V =
      (Uᴴ * U) * D * (Uᴴ * V) - (Uᴴ * V) * E * (Vᴴ * V) := by noncomm_ring
  unfold hermitianScalar
  rw [dif_pos hA, dif_pos hB]
  change (Uᴴ * (U * D * Uᴴ - V * E * Vᴴ) * V) i j = _
  rw [heq, hu, hv, Matrix.one_mul, Matrix.mul_one]
  simp only [D, E, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem hermitianScalar_frobSq_lipschitz (g : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y : ℝ, |g x - g y| ≤ L * |x - y|)
    (A B : CotangentMatrix n) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixFrobSq (hermitianScalar g A - hermitianScalar g B) ≤ L ^ 2 * matrixFrobSq (A - B) := by
  let U : CotangentMatrix n := hA.eigenvectorUnitary
  let V : CotangentMatrix n := hB.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hv : V * Vᴴ = 1 := by
    simpa only [V, Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hid (D : CotangentMatrix n) (hD : D.IsHermitian) : hermitianScalar (fun x => x) D = D := by
    rw [hermitianScalar_eq_cfc _ D hD, cfc_id' (R := ℝ) D (show IsSelfAdjoint D from hD)]
  calc
    _ = matrixFrobSq (Uᴴ * (hermitianScalar g A - hermitianScalar g B) * V) :=
      (matrixFrobSq_unitary_left_right _ U V hu hv).symm
    _ ≤ L ^ 2 * matrixFrobSq (Uᴴ *
        (hermitianScalar (fun x => x) A - hermitianScalar (fun x => x) B) * V) := by
      simp only [matrixFrobSq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [spectral_difference_sandwich_entry A B hA hB g,
        spectral_difference_sandwich_entry A B hA hB (fun x => x)]
      simp only [← Complex.ofReal_sub, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))).mpr
        (hg (hA.eigenvalues i) (hB.eigenvalues j))
      simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_right hs
        (sq_nonneg ‖(Uᴴ * V) i j‖)
    _ = _ := by rw [hid A hA, hid B hB, matrixFrobSq_unitary_left_right _ U V hu hv]

end Yau.Blueprint.V04Proof
