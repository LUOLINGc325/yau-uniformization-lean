import Yau.Proofs.V03LeviNaturality
import Yau.Proofs.V03WirtingerDirections

/-! The actual complex Hessian transforms by conjugate transpose under a
holomorphic coordinate map; every entry follows from the native derivatives. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem leviMatrix_holomorphic_comp {n : ℕ} {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    {T : E → CotangentCoord n} {f : CotangentCoord n → ℝ} {z : E}
    (hT : ContDiffAt ℂ 2 T z) (hf : ContDiffAt ℝ 2 f (T z)) (dir : ι → E) :
    leviMatrix (fun y => f (T y)) z dir =
      (Matrix.of fun (i : CotangentIndex n) (j : ι) =>
        cotangentCoordsVector (fderiv ℂ T z (dir j)) i)ᴴ *
        leviMatrix f (T z) cotangentDir *
          (Matrix.of fun (i : CotangentIndex n) (j : ι) =>
            cotangentCoordsVector (fderiv ℂ T z (dir j)) i) := by
  ext a b
  change wirt (fun y => wirtBar (fun x => (f (T x) : ℂ)) y (dir a)) z (dir b) = _
  rw [mixedWirt_holomorphic_comp hT hf]
  have hu := cotangentVectorOfCoords_coordsVector (fderiv ℂ T z (dir a))
  have hv := cotangentVectorOfCoords_coordsVector (fderiv ℂ T z (dir b))
  rw [← hu, ← hv, cotangent_levi_contraction hf, Matrix.mul_assoc]
  rfl

end Yau.Blueprint.V03Proof
