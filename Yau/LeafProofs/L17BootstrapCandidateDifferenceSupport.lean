import Yau.LeafProofs.L17BootstrapCandidateMatrices
import Yau.LeafProofs.L17BootstrapRelativeLogValues

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux
open L17BootstrapInverseHessianCoefficientsAux
local instance candidateDifferenceSupportMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}

/-- The actual relative matrix logarithm has the same zero collar as the
computed coefficients and the actual background logarithmic difference. -/
theorem candidateLogDifference_zero_on_collar (D : BootstrapPatch P x)
    {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)
    (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma) (hgamma1 : gamma≤1) (hr : P.radius≤1)
    (v : SchauderSpace P T gamma hT)
    (K Hbase H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T gamma)
    (c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (dLog : LocalHolderSpace ℝ P T gamma)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (hSmallt : ‖relativeMetricPerturbation P T gamma K Hbase H‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T gamma K Hbase
      (Hstar P hT hTime hgamma0 hgamma1 hr v)‖<1)
    (hLog : ∀q : LocalCylinder P T,
      q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump → localFun ℝ dLog q=0)
    (q : LocalCylinder P T)
    (hq : q.1≠D.center ∨ (q.2.1 : ComplexVector n)∉tsupport D.bump) :
    localFun ℝ (relativeLogDifference P T gamma K Hbase H
      (Hstar P hT hTime hgamma0 hgamma1 hr v) dLog) q=0 :=
  relativeLogDifference_zero_at P T gamma K Hbase H
    (Hstar P hT hTime hgamma0 hgamma1 hr v) dLog hSmallt hSmall0 q
    (shiftedMetric_collar D htheta hTime hgamma0 hgamma1 hr v H c0 hC0 hH q hq) (hLog q hq)

end Yau.LeafProofs.L17BootstrapMetricAux
