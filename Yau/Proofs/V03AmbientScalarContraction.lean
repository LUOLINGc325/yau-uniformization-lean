import Yau.Proofs.V03AmbientScalarDifferential
import Yau.Proofs.V03RealWirtingerDifferential
import Yau.Proofs.V03JointAmbientDifferential

/-! The genuine intrinsic scalar differential contracts its smooth
ambient covector with the actual first family derivative, including within derivatives. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem ambientScalarCovector_contract {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (b : CotangentPoint M → ℝ) (y : CotangentPoint M) (v : CotangentIndex n → ℂ) :
    ambientScalarCovector G b y ⬝ᵥ (cotangentDG G y.1 y *ᵥ v) =
      wirt (fun z => (b (cotangentChartInv y.1 z) : ℂ)) (cotangentChart y.1 y)
        (cotangentVectorOfCoords v) := by
  unfold ambientScalarCovector fixedAmbientScalarCovector
  rw [cotangentChart_left_inv y.1 (mem_extChartAt_source _),
    ambientCovector_contract (cotangentDG_gram_posDef hG y).isUnit]
  exact (cotangent_wirt_contraction _ _ v).symm

theorem cotangentHolomorphicOn_scalar_fderivWithin {n : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℝ S p)
    {b : CotangentPoint M → ℝ}
    (hb : DifferentiableAt ℝ (fun z => b (cotangentChartInv (f p).1 z))
      (cotangentChart (f p).1 (f p))) (u : P) :
    fderivWithin ℝ (fun r => b (f r)) S p u =
      fderiv ℝ (fun z => b (cotangentChartInv (f p).1 z)) (cotangentChart (f p).1 (f p))
        (fderivWithin ℂ (fun r => cotangentChart (f p).1 (f r)) S p u) := by
  have hc := (cotangentHolomorphicOn_centeredCoords_contDiffWithinAt hf hp).differentiableWithinAt (by simp)
  have hs : ∀ᶠ r in 𝓝[S] p, f r ∈ cotangentSource (f p).1 :=
    (hf.1 p hp).continuousWithinAt.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := ComplexModel n) (f p).1).mem_nhds (mem_extChartAt_source _))
  have he : (fun r => b (f r)) =ᶠ[𝓝[S] p]
      (fun r => b (cotangentChartInv (f p).1 (cotangentChart (f p).1 (f r)))) := by
    filter_upwards [hs] with r hr
    rw [cotangentChart_left_inv (f p).1 hr]
  rw [he.fderivWithin_eq_of_mem hp]
  have hh := congrArg (fun A : P →L[ℝ] ℝ => A u)
    ((hb.hasFDerivAt.comp_hasFDerivWithinAt p (hc.hasFDerivWithinAt.restrictScalars ℝ)).fderivWithin hS)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars'] using hh

theorem cotangentHolomorphicOn_scalar_ambient_fderivWithin {n q : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {p : P} (hp : p ∈ S) (hS : UniqueDiffWithinAt ℝ S p)
    {b : CotangentPoint M → ℝ}
    (hb : DifferentiableAt ℝ (fun z => b (cotangentChartInv (f p).1 z))
      (cotangentChart (f p).1 (f p))) (u : P) :
    fderivWithin ℝ (fun r => b (f r)) S p u =
      2 * (ambientScalarCovector G b (f p) ⬝ᵥ
        (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a)).re := by
  let y := f p
  let w := fderivWithin ℂ (fun r => cotangentChart y.1 (f r)) S p u
  let v := cotangentCoordsVector w
  have hy : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hV : (fun a => fderivWithin ℂ (fun r => G (f r)) S p u a) = cotangentDG G y.1 y *ᵥ v := by
    funext a
    rw [cotangentHolomorphicOn_ambient_fderivWithin hG.1 hf hp hS.mono_field y.1 hy,
      ContinuousLinearMap.comp_apply, cotangentDG_mulVec, cotangentVectorOfCoords_coordsVector]
  rw [hV, ambientScalarCovector_contract hG, cotangentVectorOfCoords_coordsVector,
    cotangentHolomorphicOn_scalar_fderivWithin hf hp hS hb u, real_fderiv_eq_two_re_wirt hb]

end Yau.Blueprint.V03Proof
