import Yau.Proofs.V03Elementary

/-! Coordinate linear algebra for the actual cotangent differential.
In particular its Gram determinant is strictly positive at an immersion. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentVectorOfCoords_coordsVector (z : CotangentCoord n) :
    cotangentVectorOfCoords (cotangentCoordsVector z) = z := by
  cases z
  rfl

theorem cotangentCoordsVector_vectorOfCoords (v : CotangentIndex n → ℂ) :
    cotangentCoordsVector (cotangentVectorOfCoords v) = v := by
  funext i
  cases i <;> rfl

theorem cotangentVectorOfCoords_injective :
    Function.Injective (cotangentVectorOfCoords :
      (CotangentIndex n → ℂ) → CotangentCoord n) := by
  intro v w h
  simpa only [cotangentCoordsVector_vectorOfCoords] using
    congrArg cotangentCoordsVector h

theorem cotangentVectorOfCoords_eq_sum (v : CotangentIndex n → ℂ) :
    cotangentVectorOfCoords v = ∑ i, v i • cotangentDir i := by
  classical
  ext j <;>
    simp [cotangentVectorOfCoords, cotangentDir, Fintype.sum_sum_type, stdVec,
      EuclideanSpace.single, Prod.fst_sum, Prod.snd_sum, WithLp.ofLp_sum,
      Finset.sum_apply, Pi.single_apply]

theorem cotangentDG_mulVec (G : CotangentPoint M → ComplexVector q)
    (x : M.Carrier) (y : CotangentPoint M) (v : CotangentIndex n → ℂ) (b : Fin q) :
    (cotangentDG G x y *ᵥ v) b =
      (fderiv ℂ (fun z => G (cotangentChartInv x z)) (cotangentChart x y)
        (cotangentVectorOfCoords v)) b := by
  rw [cotangentVectorOfCoords_eq_sum]
  simp [cotangentDG, Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]

theorem cotangentDG_mulVec_injective
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (y : CotangentPoint M) : Function.Injective (cotangentDG G y.1 y).mulVec := by
  intro v w hvw
  apply cotangentVectorOfCoords_injective
  apply hG.2.2 y
  ext b
  simpa only [← cotangentDG_mulVec] using congrFun hvw b

theorem cotangentDG_gram_posDef
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (y : CotangentPoint M) :
    ((cotangentDG G y.1 y)ᴴ * cotangentDG G y.1 y).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (cotangentDG_mulVec_injective hG y)

theorem cotangentDG_gram_det_re_pos
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (y : CotangentPoint M) :
    0 < ((cotangentDG G y.1 y)ᴴ * cotangentDG G y.1 y).det.re :=
  (Complex.pos_iff.mp (cotangentDG_gram_posDef hG y).det_pos).1

end Yau.Blueprint.V03Proof
