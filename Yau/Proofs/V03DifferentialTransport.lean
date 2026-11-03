import Yau.Proofs.V03Atlas
import Yau.Proofs.V03HolomorphicSmooth

/-! The differential of the original immersion transforms by the actual
cotangent chart derivative. This transports ambient frames to fixed charts. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

theorem cotangentDG_transition {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (x x' : M.Carrier) (y : CotangentPoint M)
    (hy : y ∈ cotangentSource x) (hy' : y ∈ cotangentSource x') :
    cotangentDG G x y = cotangentDG G x' y * cotangentTransition x x' y := by
  let z := cotangentChart x y
  let T : CotangentCoord n → CotangentCoord n :=
    fun w => cotangentChart x' (cotangentChartInv x w)
  have hz : z ∈ cotangentTarget x := cotangentChart_mapsTo x hy
  have hbase : chartInv x z.1 = y.1 := (extChartAt (ComplexModel n) x).left_inv hy
  have hz' : chartInv x z.1 ∈ (extChartAt (ComplexModel n) x').source := by
    rw [hbase]
    exact hy'
  have hT : ContDiffAt ℂ ∞ T z := cotangentChartTransition_contDiffAt x x' hz hz'
  have hTz : T z = cotangentChart x' y := by
    dsimp only [T, z]
    rw [cotangentChart_left_inv x hy]
  have htarget' : cotangentChart x' y ∈ cotangentTarget x' := cotangentChart_mapsTo x' hy'
  have hG' : DifferentiableAt ℂ (fun w => G (cotangentChartInv x' w)) (T z) := by
    rw [hTz]
    exact (hG x' _ htarget').differentiableAt
      (((isOpen_extChartAt_target (I := ComplexModel n) x').prod isOpen_univ).mem_nhds htarget')
  have heq : (fun w => G (cotangentChartInv x w)) =ᶠ[𝓝 z]
      (fun w => G (cotangentChartInv x' (T w))) := by
    filter_upwards [(isOpen_cotangentChartOverlap x x').mem_nhds ⟨hz, hz'⟩] with w hw
    exact congrArg G (cotangentChart_left_inv x' hw.2).symm
  have hderiv : fderiv ℂ (fun w => G (cotangentChartInv x w)) z =
      (fderiv ℂ (fun w => G (cotangentChartInv x' w)) (cotangentChart x' y)).comp
        (fderiv ℂ T z) := by
    rw [heq.fderiv_eq]
    have hc := fderiv_comp z hG' (hT.differentiableAt (by simp))
    simpa only [Function.comp_def, hTz] using hc
  ext a b
  change (fderiv ℂ (fun w => G (cotangentChartInv x w)) z (cotangentDir b)) a = _
  rw [hderiv, ContinuousLinearMap.comp_apply, Matrix.mul_apply]
  have hm := cotangentDG_mulVec G x' y (fun k => cotangentTransition x x' y k b) a
  simp only [Matrix.mulVec, dotProduct] at hm
  rw [hm]
  have hvec : cotangentVectorOfCoords (fun k => cotangentTransition x x' y k b) =
      fderiv ℂ T z (cotangentDir b) :=
    cotangentVectorOfCoords_coordsVector _
  rw [hvec]

theorem ambientFrame_in_fixed_chart {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentHolomorphic G) (f : ℂ → CotangentPoint M)
    (E : ℂ → CotangentMatrix n) (x : M.Carrier) (ζ : ℂ)
    (hx : f ζ ∈ cotangentSource x) :
    ambientFrame G f E ζ = cotangentDG G x (f ζ) * frameInChart x f E ζ := by
  unfold ambientFrame frameInChart
  rw [cotangentDG_transition hG (f ζ).1 x (f ζ) (mem_extChartAt_source _) hx,
    Matrix.mul_assoc]

end Yau.Blueprint.V03Proof
