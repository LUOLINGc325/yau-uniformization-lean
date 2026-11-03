import Yau.Proofs.F01MatrixCoordinateEquiv

/-! Actual invertible affine coordinates for the normalized matrix frames. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

def affineCoordinateHomeomorph (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ComplexVector n ≃ₜ ComplexVector n :=
  (matrixCoordinateEquiv A hA).toHomeomorph.trans (Homeomorph.addLeft z0)

theorem affineCoordinateHomeomorph_apply (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (z : ComplexVector n) :
    affineCoordinateHomeomorph z0 A hA z = z0 + matrixCoordinateEquiv A hA z := rfl

theorem affineCoordinateHomeomorph_inverse_apply (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (z : ComplexVector n) :
    (affineCoordinateHomeomorph z0 A hA).symm z =
      (matrixCoordinateEquiv A hA).symm (z - z0) := by
  change (matrixCoordinateEquiv A hA).symm (-z0 + z) = _
  congr 1
  abel

theorem affineCoordinateHomeomorph_contDiff (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ContDiff ℂ ∞ (affineCoordinateHomeomorph z0 A hA) := by
  change ContDiff ℂ ∞ (fun z => z0 + matrixCoordinateEquiv A hA z)
  fun_prop

theorem affineCoordinateHomeomorph_inverse_contDiff (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ContDiff ℂ ∞ (affineCoordinateHomeomorph z0 A hA).symm := by
  have he := funext (affineCoordinateHomeomorph_inverse_apply z0 A hA)
  rw [he]
  fun_prop

theorem affineCoordinateHomeomorph_hasFDerivAt (z0 : ComplexVector n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (z : ComplexVector n) :
    HasFDerivAt (affineCoordinateHomeomorph z0 A hA)
      (matrixCoordinateEquiv A hA).toContinuousLinearMap z := by
  change HasFDerivAt (fun w => z0 + matrixCoordinateEquiv A hA w) _ z
  exact (matrixCoordinateEquiv A hA).hasFDerivAt.const_add z0

end Yau.NodeProofs.F01Aux
