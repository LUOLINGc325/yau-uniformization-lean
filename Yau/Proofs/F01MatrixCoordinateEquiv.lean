import Yau.Proofs.F01NormalizeHermitian
import Yau.LeafProofs.L17ChartNaturality

/-! An invertible matrix is realized by an actual continuous complex linear
coordinate equivalence, with its native coordinate matrix unchanged. -/
noncomputable section
open scoped Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

def matrixCoordinateEquiv (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ComplexVector n ≃L[ℂ] ComplexVector n :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv
    (Units.map (Matrix.toLpLinAlgEquiv (p := 2)).toMonoidHom hA.unit)).toContinuousLinearEquiv

theorem matrixCoordinateEquiv_apply (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A)
    (v : ComplexVector n) :
    matrixCoordinateEquiv A hA v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := by
  change WithLp.toLp 2 ((hA.unit : Matrix (Fin n) (Fin n) ℂ) *ᵥ WithLp.ofLp v) = _
  rw [hA.unit_spec]

theorem matrixCoordinateEquiv_native_matrix (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A) :
    linearMatrix (matrixCoordinateEquiv A hA).toContinuousLinearMap = A := by
  ext i j
  simp only [linearMatrix, ContinuousLinearEquiv.coe_coe, matrixCoordinateEquiv_apply,
    stdVec, PiLp.ofLp_single, Matrix.mulVec_single, WithLp.ofLp_toLp, mul_one]
  simp

end Yau.NodeProofs.F01Aux
