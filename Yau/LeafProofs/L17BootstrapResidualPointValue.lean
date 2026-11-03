import Yau.LeafProofs.L17BootstrapResidualValues
import Yau.LeafProofs.L17NonlinearResidual

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17LocalHolderBanachAlgebraAux
local instance residualPointValueMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T)
variable (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)

theorem scalarNonlinearResidualMap_value_of_positive (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ v, holderFun (J v)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P v)
    (u : SchauderSpace P T gamma hT)
    (hu : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖<1)
    (hPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1+coordinateMetricError u q).PosDef)
    (q : Cylinder M T) :
    holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J u) q=
      timeFun u q-Real.log ((potentialMetricMatrix u q).det.re/(gMat g q.1).det.re) := by
  have hN := congrFun
    (globalNonlinearMap_value_of_positive P T gamma hT hTime hgamma0 hgamma1 hr hg J hJ u hu hPos).1 q
  change holderFun (scalarParabolicCLM P T gamma hT hTime hgamma1 hr u) q-
    holderFun (globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u) q=_
  rw [scalarParabolicCLM_value,hN]
  change timeFun u q-actualLaplacian u q-
    (Real.log ((potentialMetricMatrix u q).det.re/(gMat g q.1).det.re)-actualLaplacian u q)=_
  ring

end Yau.LeafProofs.L17BootstrapMetricAux
