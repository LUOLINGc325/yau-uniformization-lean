import Yau.Proofs.F01OrdinaryCharts
import Yau.Proofs.F01MixedJetLocality
import Yau.LeafProofs.L17ChartNaturality
import Yau.LeafProofs.L22Locality

/-! The actual ordinary inverse chart recovers the native fixed-chart
matrix and its genuine logarithmic Hessian. -/
noncomputable section
open Set Filter
open scoped Topology Manifold Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem ordinaryChart_pullbackMatrix (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    pullbackMatrix g (ordinaryChart x) z = hMat g x z := by
  ext i j
  change chartGramCoefficient g (ordinaryChart x) z i j = hMat g x z i j
  exact ordinaryChart_Gram g x hz i j

theorem ordinaryChart_pullbackMatrix_center (g : HermitianField M) (x : M.Carrier) :
    pullbackMatrix g (ordinaryChart x) (chartPt x x) = gMat g x :=
  ordinaryChart_pullbackMatrix g x (mem_extChartAt_target x)

theorem ordinaryChart_logdet_levi (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    leviC (fun w => Real.log (pullbackMatrix g (ordinaryChart x) w).det.re) z =
      leviC (logDet g x) z := by
  apply Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
  rw [ordinaryChart_pullbackMatrix g x hw]
  rfl

end Yau.NodeProofs.F01Aux
