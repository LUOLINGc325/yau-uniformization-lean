import Yau.Proofs.V03JointBaseDifferential

/-! The base component of the actual full cotangent transition derivative
is exactly the original base tangent coordinate change. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentTransition_fderiv_base {n : ℕ} {M : ComplexManifold n}
    (x x' : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') (v : CotangentCoord n) :
    (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z)) (cotangentChart x y) v).1 =
      tangentCoordChange (ComplexModel n) x x' y.1 v.1 := by
  let z := cotangentChart x y
  let T : CotangentCoord n → CotangentCoord n := fun w => cotangentChart x' (cotangentChartInv x w)
  let B : ComplexVector n → ComplexVector n := fun w => chartPt x' (chartInv x w)
  have hb : chartInv x z.1 = y.1 := (extChartAt (ComplexModel n) x).left_inv hy
  have hT : DifferentiableAt ℂ T z :=
    (cotangentChartTransition_contDiffAt x x' (cotangentChart_mapsTo x hy)
      (by rw [hb]; exact hy')).differentiableAt (by simp)
  have hB : DifferentiableAt ℂ B z.1 :=
    (chartTransition_contDiffAt x x' (cotangentChart_mapsTo x hy).1
      (by rw [hb]; exact hy')).differentiableAt (by simp)
  have hd := hT.hasFDerivAt.fst.unique
    (hB.hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℂ)))
  have he := congrArg (fun A : CotangentCoord n →L[ℂ] ComplexVector n => A v) hd
  have hDB := chartTransition_fderiv_eq_coordChange x x' (cotangentChart_mapsTo x hy).1
  rw [hb] at hDB
  change (fderiv ℂ T z v).1 = fderiv ℂ B z.1 v.1 at he
  change fderiv ℂ B z.1 = tangentCoordChange (ComplexModel n) x x' y.1 at hDB
  rw [hDB] at he
  exact he

end Yau.Blueprint.V03Proof
