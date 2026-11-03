import Yau.Proofs.D05CotangentModel

/-! The full Hessian block of an induced cotangent coordinate change.
Its lower-left block is H A, with H symmetric over the complex field. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

variable {n : ℕ}

theorem complexVector_basis_sum (v : ComplexVector n) : (∑ i, v i • stdVec i) = v := by
  ext i
  simp [stdVec, EuclideanSpace.single, Pi.single_apply]

theorem complexLinearMatrix_id :
    complexLinearMatrix (ContinuousLinearMap.id ℂ (ComplexVector n)) = 1 := by
  ext i j
  simp [complexLinearMatrix, stdVec, EuclideanSpace.single, Pi.single_apply, Matrix.one_apply, eq_comm]

theorem complexLinearMatrix_comp {m b : ℕ}
    (L : ComplexVector n →L[ℂ] ComplexVector m)
    (K : ComplexVector b →L[ℂ] ComplexVector n) :
    complexLinearMatrix (L.comp K) = complexLinearMatrix L * complexLinearMatrix K := by
  ext i j
  change L (K (stdVec j)) i = ∑ k, L (stdVec k) i * K (stdVec j) k
  conv_lhs => rw [← complexVector_basis_sum (K (stdVec j)), map_sum]
  simp [map_smul, mul_comm]

theorem cotangentModel_hessian_mul (ψ : ComplexVector n → ComplexVector n)
    (u ξ : ComplexVector n) (L : ComplexVector n →L[ℂ] ComplexVector n) (i j : Fin n) :
    (∑ k, (fderiv ℂ (fderiv ℂ ψ) u (L (stdVec j)) (stdVec i)) k * ξ k) =
      (cotangentModelHessian ψ u ξ * complexLinearMatrix L) i j := by
  conv_lhs => rw [← complexVector_basis_sum (L (stdVec j)), map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply, smul_apply, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, cotangentModelHessian, complexLinearMatrix, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem cotangentModelHessian_transpose {ψ : ComplexVector n → ComplexVector n}
    {u : ComplexVector n} (hψ : ContDiffAt ℂ ∞ ψ u) (ξ : ComplexVector n) :
    (cotangentModelHessian ψ u ξ)ᵀ = cotangentModelHessian ψ u ξ := by
  have hs := hψ.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.transpose_apply, cotangentModelHessian]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun v : ComplexVector n => v k * ξ k) (hs (stdVec i) (stdVec j))

def cotangentModelJacobian (φ ψ : ComplexVector n → ComplexVector n)
    (z : CotangentCoord n) : CotangentMatrix n :=
  fun i j => cotangentCoordsVector (fderiv ℂ (modelCotangentChange φ ψ) z (cotangentDir j)) i

theorem cotangentModelJacobian_blocks {φ ψ : ComplexVector n → ComplexVector n}
    {z : CotangentCoord n} (hφ : ContDiffAt ℂ ∞ φ z.1)
    (hψ : ContDiffAt ℂ ∞ ψ (φ z.1)) :
    cotangentModelJacobian φ ψ z = Matrix.fromBlocks
      (complexLinearMatrix (fderiv ℂ φ z.1)) 0
      (cotangentModelHessian ψ (φ z.1) z.2 * complexLinearMatrix (fderiv ℂ φ z.1))
      (complexLinearMatrix (fderiv ℂ ψ (φ z.1)))ᵀ := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change (fderiv ℂ (modelCotangentChange φ ψ) z (stdVec j, 0)).1 i = _
          rw [modelCotangentChange_fderiv_fst hφ hψ]
          rfl
      | inr j =>
          change (fderiv ℂ (modelCotangentChange φ ψ) z (0, stdVec j)).1 i = 0
          rw [modelCotangentChange_fderiv_fst hφ hψ]
          simp
  | inr i =>
      cases j with
      | inl j =>
          change (fderiv ℂ (modelCotangentChange φ ψ) z (stdVec j, 0)).2 i = _
          rw [modelCotangentChange_fderiv_snd hφ hψ]
          simp only [Prod.fst, Prod.snd, PiLp.zero_apply, mul_zero, add_zero]
          exact cotangentModel_hessian_mul ψ (φ z.1) z.2 (fderiv ℂ φ z.1) i j
      | inr j =>
          change (fderiv ℂ (modelCotangentChange φ ψ) z (0, stdVec j)).2 i = _
          rw [modelCotangentChange_fderiv_snd hφ hψ]
          simp [complexLinearMatrix, stdVec, EuclideanSpace.single, Pi.single_apply]

theorem cotangentModelJacobian_symplectic {φ ψ : ComplexVector n → ComplexVector n}
    {z : CotangentCoord n} (hφ : ContDiffAt ℂ ∞ φ z.1)
    (hψ : ContDiffAt ℂ ∞ ψ (φ z.1))
    (hinv : (fderiv ℂ φ z.1).comp (fderiv ℂ ψ (φ z.1)) = ContinuousLinearMap.id ℂ _) :
    cotangentModelJacobian φ ψ z * canonicalBivector *
      (cotangentModelJacobian φ ψ z)ᵀ = (canonicalBivector : CotangentMatrix n) := by
  let A := complexLinearMatrix (fderiv ℂ φ z.1)
  let K := complexLinearMatrix (fderiv ℂ ψ (φ z.1))
  let H := cotangentModelHessian ψ (φ z.1) z.2
  have hAK : A * K = 1 := by
    rw [← complexLinearMatrix_comp, hinv, complexLinearMatrix_id]
  have hH : Hᵀ = H := cotangentModelHessian_transpose hψ z.2
  have hC : (H * A) * (Kᵀ)ᵀ = H := by
    rw [Matrix.transpose_transpose, Matrix.mul_assoc, hAK, Matrix.mul_one]
  have hCt : Kᵀ * (H * A)ᵀ = H := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hH] using
      congrArg Matrix.transpose hC
  rw [cotangentModelJacobian_blocks hφ hψ]
  exact canonicalBivector_block_symplectic A Kᵀ (H * A)
    (by rw [Matrix.transpose_transpose]; exact hAK) (hC.trans hCt.symm)

end Yau.Blueprint.D05Proof
