import Yau.Proofs.V03AmbientBaseTensor
import Yau.Proofs.V03AmbientTensorVector
import Yau.Proofs.V03JointBaseTwoForm
import Yau.Proofs.V03JointAmbientDifferential

/-! The actual base variation diagonal contracts its one intrinsic
ambient metric tensor with the actual first ambient family velocity. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem jointBaseTwoForm_ambient_diagonal {n q : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G) (h : HermitianField M)
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p) (u : P) :
    jointBaseTwoForm h f S p ![u, Complex.I • u] =
      2 * (star (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a) ⬝ᵥ
        (ambientBaseTensor G h (f p) *ᵥ fun a => fderivWithin ℂ (fun r => G (f r)) S p u a)).re := by
  let y := f p
  let w := fderivWithin ℂ (fun r => cotangentChart y.1 (f r)) S p u
  let v := cotangentCoordsVector w
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround : chartInv y.1 (cotangentChart y.1 y).1 = y.1 :=
    (extChartAt (ComplexModel n) y.1).left_inv hy
  have hcoord := (cotangentHolomorphicOn_centeredCoords_contDiffWithinAt hf hp).differentiableWithinAt (by simp)
  have hbase : fderivWithin ℂ (fun r => chartPt y.1 (f r).1) S p u = w.1 := by
    have hh := congrArg (fun A : P →L[ℂ] ComplexVector n => A u)
      (hcoord.hasFDerivWithinAt.fst.fderivWithin hS)
    exact hh
  have hV : (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a) = cotangentDG G y.1 y *ᵥ v := by
    funext a
    rw [cotangentHolomorphicOn_ambient_fderivWithin hG.1 hf hp hS y.1 hy,
      ContinuousLinearMap.comp_apply, cotangentDG_mulVec, cotangentVectorOfCoords_coordsVector]
  rw [hV, ambientBaseTensor, fixedAmbientBaseTensor, cotangentChart_left_inv y.1 hy,
    ambientLeviTensor_vector (cotangentDG_gram_posDef hG y).isUnit,
    baseCotangentMatrix_contract, cotangentVectorOfCoords_coordsVector, hround]
  rw [jointBaseTwoForm, twoForm_pullback_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  rw [chartKahlerTwoForm, matrixKahlerTwoForm_diagonal (hMat_isHermitian h _ _), hbase,
    hMat_pair]
  rw [show chartInv (f p).1 (chartPt (f p).1 (f p).1) = (f p).1 from
    (extChartAt (ComplexModel n) (f p).1).left_inv (mem_extChartAt_source _)]

end Yau.Blueprint.V03Proof
