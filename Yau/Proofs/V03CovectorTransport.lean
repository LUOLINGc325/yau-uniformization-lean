import Yau.Proofs.V03ClearedLogCovector
import Yau.Proofs.V03SpatialHessianTransport

/-! First Wirtinger covectors transform by the actual holomorphic
cotangent differential. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem wirt_holomorphic_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : E → F} {f : F → ℂ} {z : E} (hT : DifferentiableAt ℂ T z)
    (hf : DifferentiableAt ℝ f (T z)) (v : E) :
    wirt (fun y => f (T y)) z v = wirt f (T z) (fderiv ℂ T z v) := by
  have hD := fderiv_comp z hf (hT.restrictScalars ℝ)
  simp only [Function.comp_def] at hD
  simp only [wirt, hD, ContinuousLinearMap.comp_apply, hT.fderiv_restrictScalars ℝ,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

theorem cotangent_wirt_contraction {n : ℕ} (f : CotangentCoord n → ℂ)
    (z : CotangentCoord n) (v : CotangentIndex n → ℂ) :
    wirt f z (cotangentVectorOfCoords v) = (fun i => wirt f z (cotangentDir i)) ⬝ᵥ v := by
  rw [cotangentVectorOfCoords_eq_sum, wirt_sum_direction]
  simp only [wirt_smul_direction, dotProduct, mul_comm]

theorem scalarWirt_in_fixed_chart {n : ℕ} {M : ComplexManifold n}
    (b : CotangentPoint M → ℝ) (x : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x)
    (hb : DifferentiableAt ℝ (fun z => b (cotangentChartInv x z)) (cotangentChart x y)) :
    (fun i => wirt (fun z => (b (cotangentChartInv y.1 z) : ℂ))
      (cotangentChart y.1 y) (cotangentDir i)) =
      (fun i => wirt (fun z => (b (cotangentChartInv x z) : ℂ))
        (cotangentChart x y) (cotangentDir i)) ᵥ* cotangentTransition y.1 x y := by
  let z0 := cotangentChart y.1 y
  let T : CotangentCoord n → CotangentCoord n := fun z => cotangentChart x (cotangentChartInv y.1 z)
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hz : z0 ∈ cotangentTarget y.1 := cotangentChart_mapsTo y.1 hself
  have hbase : chartInv y.1 z0.1 = y.1 := (extChartAt (ComplexModel n) y.1).left_inv hself
  have hz' : chartInv y.1 z0.1 ∈ (extChartAt (ComplexModel n) x).source := by
    rw [hbase]
    exact hy
  have hT := cotangentChartTransition_contDiffAt y.1 x hz hz'
  have hTz : T z0 = cotangentChart x y := by
    dsimp only [T, z0]
    rw [cotangentChart_left_inv y.1 hself]
  have heq : (fun z => (b (cotangentChartInv y.1 z) : ℂ)) =ᶠ[𝓝 z0]
      (fun z => (b (cotangentChartInv x (T z)) : ℂ)) := by
    filter_upwards [(isOpen_cotangentChartOverlap y.1 x).mem_nhds ⟨hz, hz'⟩] with z hz
    exact congrArg (fun u => (b u : ℂ)) (cotangentChart_left_inv x hz.2).symm
  have hbC : DifferentiableAt ℝ (fun z => (b (cotangentChartInv x z) : ℂ)) (T z0) := by
    rw [hTz]
    exact Complex.ofRealCLM.differentiableAt.comp _ hb
  funext i
  have he : wirt (fun z => (b (cotangentChartInv y.1 z) : ℂ)) z0 (cotangentDir i) =
      wirt (fun z => (b (cotangentChartInv x (T z)) : ℂ)) z0 (cotangentDir i) := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [he, wirt_holomorphic_comp (T := T) (hT.differentiableAt (by simp)) hbC]
  change wirt (fun z => (b (cotangentChartInv x z) : ℂ)) (T z0)
    (fderiv ℂ T z0 (cotangentDir i)) = _
  rw [hTz,
    ← cotangentVectorOfCoords_coordsVector (fderiv ℂ T z0 (cotangentDir i)),
    cotangent_wirt_contraction]
  rfl

end Yau.Blueprint.V03Proof
