import Yau.Proofs.V03LeviMatrixTransport
import Yau.Proofs.V03TransitionInverse

/-! The original centered-atlas spatial Hessian transforms to every valid
fixed cotangent chart by the actual transition differential. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem spatialHessian_in_fixed_chart {n : ℕ} {X : KahlerManifold n}
    (b : CotangentPoint X.manifold → ℝ) (x : Pt X) {y : CotangentPoint X.manifold}
    (hy : y ∈ cotangentSource x)
    (hb : ContDiffAt ℝ 2 (fun z => b (cotangentChartInv x z)) (cotangentChart x y)) :
    spatialHessian b y = (cotangentTransition y.1 x y)ᴴ *
      leviMatrix (fun z => b (cotangentChartInv x z)) (cotangentChart x y) cotangentDir *
        cotangentTransition y.1 x y := by
  let z0 := cotangentChart y.1 y
  let T : CotangentCoord n → CotangentCoord n := fun z =>
    cotangentChart x (cotangentChartInv y.1 z)
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hz : z0 ∈ cotangentTarget y.1 := cotangentChart_mapsTo y.1 hself
  have hbase : chartInv y.1 z0.1 = y.1 :=
    (extChartAt (ComplexModel n) y.1).left_inv hself
  have hz' : chartInv y.1 z0.1 ∈ (extChartAt (ComplexModel n) x).source := by
    rw [hbase]
    exact hy
  have hT : ContDiffAt ℂ ∞ T z0 := cotangentChartTransition_contDiffAt y.1 x hz hz'
  have hTz : T z0 = cotangentChart x y := by
    dsimp only [T, z0]
    rw [cotangentChart_left_inv y.1 hself]
  have heq : (fun z => (b (cotangentChartInv y.1 z) : ℂ)) =ᶠ[𝓝 z0]
      (fun z => (b (cotangentChartInv x (T z)) : ℂ)) := by
    filter_upwards [(isOpen_cotangentChartOverlap y.1 x).mem_nhds ⟨hz, hz'⟩] with z hz
    exact congrArg (fun u => (b u : ℂ)) (cotangentChart_left_inv x hz.2).symm
  have hbf : ContDiffAt ℝ 2 (fun z => b (cotangentChartInv x z)) (T z0) := by
    rw [hTz]
    exact hb
  have hmatrix := leviMatrix_holomorphic_comp (hT.of_le (by simp)) hbf cotangentDir
  rw [hTz] at hmatrix
  have hleft : spatialHessian b y =
      leviMatrix (fun z => b (cotangentChartInv x (T z))) z0 cotangentDir := by
    ext i j
    exact mixedWirt_congr heq (cotangentDir i) (cotangentDir j)
  rw [hleft, hmatrix]
  rfl

end Yau.Blueprint.V03Proof
