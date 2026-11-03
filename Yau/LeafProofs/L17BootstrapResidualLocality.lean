import Yau.LeafProofs.L17BootstrapResidualLocalityBasic
import Yau.LeafProofs.L17BootstrapResidualPointValue

/-! Actual residual locality in the positive series domain, independent of transport macros. -/
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace Yau.LeafProofs.L17BootstrapResidualLocalityAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapPatchAux L17BootstrapMetricAux

local instance residualLocalityCanonicalMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Actual spatial germ and time-jet identities give equality of the actual residual values. -/
theorem scalarResidual_value_eq_of_spatial_germ
    (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hr : P.radius ≤ 1) (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w) = L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u v : SchauderSpace P T gamma hT)
    (huZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖ < 1)
    (hvZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr v‖ < 1)
    (huPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1 + coordinateMetricError u q).PosDef)
    (hvPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1 + coordinateMetricError v q).PosDef)
    (q : Cylinder M T)
    (hGerm : (fun y => schauderFun v (y,q.2)) =ᶠ[𝓝 q.1]
      (fun y => schauderFun u (y,q.2)))
    (hTimePoint : timeFun v q = timeFun u q) :
    holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v) q =
      holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J u) q := by
  rw [scalarNonlinearResidualMap_value_of_positive P T gamma hT hTime hgamma0 hgamma1 hr
    hg J hJ v hvZ hvPos q,
    scalarNonlinearResidualMap_value_of_positive P T gamma hT hTime hgamma0 hgamma1 hr
      hg J hJ u huZ huPos q,
    potentialMetricMatrix_eq_of_spatial_germ P T gamma hT u v q hGerm,hTimePoint]

/-- The original equation forces the actual transported residual to vanish outside physical support. -/
theorem scalarResidual_zero_off_patch
    (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T)
    (hTime : T ≤ P.radius^2) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hr : P.radius ≤ 1) (hg : MetricSmooth g)
    (J : LocalHolderSpace ℝ P T gamma →L[ℝ] HolderSpace P T gamma)
    (hJ : ∀ w, holderFun (J w) = L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u v : SchauderSpace P T gamma hT)
    (huZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr u‖ < 1)
    (hvZ : ‖normalizedMetricPerturbation P T gamma hT hTime hgamma0 hgamma1 hr v‖ < 1)
    (huPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1 + coordinateMetricError u q).PosDef)
    (hvPos : ∀ q : LocalCylinder P T,
      (pullbackMatrix g (P.charts.chart q.1) q.2.1 + coordinateMetricError v q).PosDef)
    {x : M.Carrier} (D : BootstrapPatch P x) (theta : ComplexVector n)
    (hValue : ∀ (y : M.Carrier) (t : Time T),
      schauderFun v (y,t) = schauderFun u (D.forward theta y,t))
    (hTimeValue : ∀ q : Cylinder M T,
      timeFun v q = timeFun u (D.forward theta q.1,q.2))
    (hEquation : scalarParabolicCLM P T gamma hT hTime hgamma1 hr u =
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u)
    (y : M.Carrier) (hy : y ∉ D.supportSet) (t : Time T) :
    holderFun (scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J v) (y,t) = 0 := by
  have hGerm := patch_spatial_germ_of_transport_values P T gamma hT u v D theta hValue y hy t
  have hTimePoint : timeFun v (y,t) = timeFun u (y,t) := by
    simpa only [D.forward_eq_self_of_not_mem_support theta hy] using hTimeValue (y,t)
  have hValues := scalarResidual_value_eq_of_spatial_germ P T gamma hT hTime hgamma0 hgamma1 hr
    hg J hJ u v huZ hvZ huPos hvPos (y,t) hGerm hTimePoint
  have hZero : scalarNonlinearResidualMap P T gamma hT hTime hgamma0 hgamma1 hr J u = 0 := by
    change scalarParabolicCLM P T gamma hT hTime hgamma1 hr u -
      globalNonlinearMap P T gamma hT hTime hgamma0 hgamma1 hr J u = 0
    rw [hEquation,sub_self]
  rw [hValues,hZero]
  rfl

end Yau.LeafProofs.L17BootstrapResidualLocalityAux
