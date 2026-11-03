import Yau.Proofs.V03BaseCotangentMatrix
import Yau.Proofs.V03CotangentBaseProjection

/-! The original base Hermitian metric, written on full cotangent
coordinates, transforms by the actual cotangent transition matrix. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem baseCotangentMatrix_chart_change {n : ℕ} {M : ComplexManifold n}
    (h : HermitianField M) (x x' : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    baseCotangentMatrix h x (cotangentChart x y) =
      (cotangentTransition x x' y)ᴴ * baseCotangentMatrix h x' (cotangentChart x' y) *
        cotangentTransition x x' y := by
  have hbx : chartInv x (cotangentChart x y).1 = y.1 := (extChartAt (ComplexModel n) x).left_inv hy
  have hbx' : chartInv x' (cotangentChart x' y).1 = y.1 := (extChartAt (ComplexModel n) x').left_inv hy'
  have hcol (a : CotangentIndex n) :
      (cotangentVectorOfCoords (fun i => cotangentTransition x x' y i a)).1 =
        tangentCoordChange (ComplexModel n) x x' y.1 (cotangentDir a).1 := by
    change (cotangentVectorOfCoords (cotangentCoordsVector
      (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z))
        (cotangentChart x y) (cotangentDir a)))).1 = _
    rw [cotangentVectorOfCoords_coordsVector]
    exact cotangentTransition_fderiv_base x x' hy hy' (cotangentDir a)
  ext a b
  have hh := baseCotangentMatrix_contract h x' (cotangentChart x' y)
    (fun i => cotangentTransition x x' y i a) (fun i => cotangentTransition x x' y i b)
  rw [hbx', hcol a, hcol b, chartVec_transition x' x y.1 hy' hy,
    chartVec_transition x' x y.1 hy' hy] at hh
  rw [baseCotangentMatrix_entry, hbx, Matrix.mul_assoc]
  exact hh.symm

end Yau.Blueprint.V03Proof
