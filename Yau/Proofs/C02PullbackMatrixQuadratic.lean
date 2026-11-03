import Yau.Proofs.C02Frames
import Yau.LeafProofs.L12
import Yau.Proofs.C02ComplexCoordinateDifferential

/-! The matrix in the original chart contract is the genuine Hermitian
Gram matrix of the supplied complex manifold differential. -/

noncomputable section
open scoped Manifold Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pullbackMat_isHermitian (h : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z : ComplexVector n) :
    (pullbackMat h Φ z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  exact ((h (Φ z)).conjugate_symmetric _ _).symm

theorem pullbackMat_quadratic (h : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (z u : ComplexVector n) :
    star (WithLp.ofLp u) ⬝ᵥ (pullbackMat h Φ z *ᵥ WithLp.ofLp u) =
      (h (Φ z)).toFun
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u)
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z u) := by
  let D := complexCoordinateDifferential Φ z
  have hsum : (∑ i, u i • D (stdVec i)) = D u := by
    simpa only [map_sum, map_smul] using congrArg D (complexVector_basis_sum u)
  have hGram : star (WithLp.ofLp u) ⬝ᵥ (pullbackMat h Φ z *ᵥ WithLp.ofLp u) =
      (h (Φ z)).toFun (∑ i, u i • D (stdVec i)) (∑ i, u i • D (stdVec i)) := by
    have hEntry (i j : Fin n) : pullbackMat h Φ z i j =
        (h (Φ z)).toFun (D (stdVec i)) (D (stdVec j)) := rfl
    rw [hermitian_sum_left]
    simp only [hermitian_sum_right, HermitianInnerProduct.map_smul_left,
      HermitianInnerProduct.map_smul_right, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.mul_sum, hEntry]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum] at hGram
  exact hGram

end Yau.Blueprint.C02Proof
