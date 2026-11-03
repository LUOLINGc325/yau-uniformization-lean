import Yau.Proofs.C05ScalarHarnackScaling
import Yau.Proofs.C05ThirdScalarTimeDefinitions

/-! The three intrinsic scalar sources use only the same actual metric and its computed curvature. -/
noncomputable section
namespace Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau Yau.Proofs.C05Aux Yau.Proofs.C05ThirdScalarTimeAux
variable {n : ℕ} {M : ComplexManifold n}

def scalarTimeSource1 (k : HermitianField M) (x : M.Carrier) : ℝ := scalarHarnackSource k 0 x

def scalarTimeSource2 (k : HermitianField M) (x : M.Carrier) : ℝ :=
  laplacian k (scalarTimeSource1 k) x +
    3 * ricciLeviPairing k (scalarCurvature k) x + 2 * ricciCube k x

def scalarTimeSource3 (k : HermitianField M) (x : M.Carrier) : ℝ :=
  laplacian k (scalarTimeSource2 k) x +
    4 * ricciLeviPairing k (scalarTimeSource1 k) x +
    12 * ricciSquareLevi k x + 3 * leviScalarSquare k x + 6 * ricciQuartic k x

end Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
