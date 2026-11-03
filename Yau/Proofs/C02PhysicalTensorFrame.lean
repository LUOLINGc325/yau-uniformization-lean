import Yau.Proofs.C02RealFrameCoordinates
import Yau.LeafProofs.L23TensorMultilinear

noncomputable section
open scoped Matrix
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem tensorFrameTransform_physicalUnitary (S : Matrix (Fin n) (Fin n) ℂ)
    (A : CovTensor n r) (I : Fin r → RIdx n) :
    tensorFrameTransform (physicalUnitaryRealMatrix S) A I =
      (Real.sqrt (2 : ℝ))⁻¹ ^ r *
        tensorEvalCLM A (fun j => complexMatrixVector S (realVec (I j))) := by
  let a := (Real.sqrt (2 : ℝ))⁻¹
  have hEval : tensorFrameTransform (physicalUnitaryRealMatrix S) A I =
      tensorEvalCLM A (fun j => a • complexMatrixVector S (realVec (I j))) := by
    dsimp only [a]
    rw [tensorEvalCLM_apply]
    simp_rw [← physicalUnitaryRealMatrix_entry]
    rfl
  rw [hEval]
  have he := (tensorEvalCLM A).map_smul_univ (fun _ => a)
    (fun j => complexMatrixVector S (realVec (I j)))
  simpa only [a, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using he

end Yau.Blueprint.C02Proof
