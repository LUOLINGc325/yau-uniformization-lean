import Yau.Proofs.C05ScalarHarnackEvolution

/-! Actual trace polynomials in the inverse metric, Ricci and Levi scalar. -/
noncomputable section
open scoped Manifold Topology ContDiff
namespace Yau.Proofs.C05ThirdScalarTimeAux
open Yau Yau.Proofs.C05Aux
variable {n : ℕ} {M : ComplexManifold n}

def ricciSquareLevi (k : HermitianField M) (x : M.Carrier) : ℝ :=
  (((gMat k x)⁻¹ * ricci k x) * ((gMat k x)⁻¹ * ricci k x) *
    ((gMat k x)⁻¹ * levi (scalarCurvature k) x)).trace.re

def leviScalarSquare (k : HermitianField M) (x : M.Carrier) : ℝ :=
  (((gMat k x)⁻¹ * levi (scalarCurvature k) x) *
    ((gMat k x)⁻¹ * levi (scalarCurvature k) x)).trace.re

def ricciQuartic (k : HermitianField M) (x : M.Carrier) : ℝ :=
  (((gMat k x)⁻¹ * ricci k x) * ((gMat k x)⁻¹ * ricci k x) *
    ((gMat k x)⁻¹ * ricci k x) * ((gMat k x)⁻¹ * ricci k x)).trace.re

end Yau.Proofs.C05ThirdScalarTimeAux
