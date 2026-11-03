import Yau.LeafProofs.L17BootstrapMetricCoefficients
import Yau.LeafProofs.L17BootstrapPositiveBaseHolder

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17LocalHolderBanachAlgebraAux
open L17BootstrapPositiveBaseHolderAux
local instance metricBaseMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable (P : UniformChartPartition g) {T gamma : ℝ}
variable (hT : 0<T) (hTime : T≤P.radius^2) (hgamma0 : 0≤gamma)
  (hgamma1 : gamma≤1) (hr : P.radius≤1)

theorem metricFromCoefficients_unshifted (u : SchauderSpace P T gamma hT) :
    metricFromCoefficients P T gamma hT (Hstar P hT hTime hgamma0 hgamma1 hr 0) 0
      (const (D2 n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) P T gamma (leviHessianCLM n)) u =
      Hstar P hT hTime hgamma0 hgamma1 hr u := by
  rw [metricFromCoefficients,metricPotentialCLM_unshifted]
  unfold Hstar
  rw [(potentialLeviBanachCLM P T gamma hT).map_zero]
  abel

theorem Hstar_isHermitian (u : SchauderSpace P T gamma hT) (q : LocalCylinder P T) :
    (Hstar P hT hTime hgamma0 hgamma1 hr u q).IsHermitian := by
  rw [Hstar_value]
  have hz : (q.2.1 : ComplexVector n)∈ball (0 : ComplexVector n) P.charts.radius :=
    (ball_subset_ball P.radius_lt.le) q.2.1.property
  have hG := pullbackMatrix_posDef g (P.charts.chart q.1) (P.charts.differentiable q.1)
    (P.charts.inverse_differentiable q.1) (P.charts.closedBall_source q.1 (ball_subset_closedBall hz))
  exact hG.isHermitian.add (coordinateMetricError_isHermitian u q)

end Yau.LeafProofs.L17BootstrapMetricAux
