import Yau.Proofs.V03AmbientGaussTensor
import Yau.Proofs.V03AmbientTensorVector
import Yau.Proofs.V03JointGaussTwoForm
import Yau.Proofs.V03JointAmbientDifferential

/-! The genuine Gauss variation diagonal contracts the one actual
ambient Gauss tensor with the actual first ambient family velocity. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem jointGaussTwoForm_ambient_diagonal {n q : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℂ S p) (u : P) :
    jointGaussTwoForm G f S p ![u, Complex.I • u] =
      2 * (star (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a) ⬝ᵥ
        (ambientGaussTensor G (f p) *ᵥ fun a => fderivWithin ℂ (fun r => G (f r)) S p u a)).re := by
  let y := f p
  let w := fderivWithin ℂ (fun r => cotangentChart y.1 (f r)) S p u
  let v := cotangentCoordsVector w
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hpot := (gaussPotential_contDiffAt hG y.1 (cotangentChart_mapsTo y.1 hy)).of_le
    (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hV : (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a) = cotangentDG G y.1 y *ᵥ v := by
    funext a
    rw [cotangentHolomorphicOn_ambient_fderivWithin hG.1 hf hp hS y.1 hy,
      ContinuousLinearMap.comp_apply, cotangentDG_mulVec, cotangentVectorOfCoords_coordsVector]
  rw [hV, ambientGaussTensor, fixedAmbientGaussTensor, cotangentChart_left_inv y.1 hy,
    ambientLeviTensor_vector (cotangentDG_gram_posDef hG y).isUnit]
  rw [jointGaussTwoForm, twoForm_pullback_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]
  rw [scalarLeviTwoForm_diagonal hpot]
  have hh := cotangent_levi_contraction hpot v v
  rw [cotangentVectorOfCoords_coordsVector] at hh
  exact congrArg (fun z : ℂ => 2 * z.re) hh

end Yau.Blueprint.V03Proof
