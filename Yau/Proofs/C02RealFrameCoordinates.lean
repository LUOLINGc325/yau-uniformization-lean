import Yau.Proofs.C02RealUnitaryMatrix
import Yau.LeafProofs.L12

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
open Yau.NodeProofs.G01Aux Yau.LeafProofs.L12Aux
variable {n : ℕ}

def complexMatrixVector (S : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) : ComplexVector n :=
  Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis S v

theorem complexMatrixVector_apply (S : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexVector n) (i : Fin n) : complexMatrixVector S v i = (S *ᵥ WithLp.ofLp v) i :=
  complexMatrix_toLin_apply S v i

theorem rawReal_entry_coordinates (S : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    rawReal S a b = realCoord (complexMatrixVector S (realVec b)) a := by
  have he := real_toMatrix_complex_toLin S a b
  rw [LinearMap.toMatrix_apply] at he
  simp only [realVec_basis_repr, LinearMap.restrictScalars_apply, realVec_basis_apply] at he
  exact he.symm

theorem physicalUnitaryRealMatrix_entry (S : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    physicalUnitaryRealMatrix S a b =
      realCoord ((Real.sqrt (2 : ℝ))⁻¹ • complexMatrixVector S (realVec b)) a := by
  rw [physicalUnitaryRealMatrix, Matrix.smul_apply, smul_eq_mul, rawReal_entry_coordinates]
  simp only [← realCoordCLM_apply, map_smul, smul_eq_mul]

end Yau.Blueprint.C02Proof
