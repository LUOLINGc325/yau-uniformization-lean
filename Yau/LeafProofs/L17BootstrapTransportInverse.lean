import Yau.LeafProofs.L17BootstrapTransportTime
import Yau.LeafProofs.L17BootstrapMetricLocalFormula

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
open L17BootstrapMetricAux L17BootstrapInverseHessianCoefficientsAux L17SmallTranslationAux
local instance transportInverseMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}
variable (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
  (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
  (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
  (hgamma0 : 0<gamma) (hgamma1 : gamma≤1)
  (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)
local notation "Transport" => patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta
local notation "Psi" => cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta

theorem patchTransportCLM_inverse_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (Transport u) (D.inverse theta q.1,q.2)=schauderFun u q := by
  rw [patchTransportCLM_value,D.forward_inverse htheta]

theorem patchTransportCLM_inverseChart (u : SchauderSpace P T gamma hT) (t : Time T)
    {y : ComplexVector n} (hy : y∈(P.charts.chart D.center).source) :
    chartFunction (Transport u) D.center t (Psi y)=chartFunction u D.center t y := by
  change schauderFun (Transport u) (P.charts.chart D.center (Psi y),t)=
    schauderFun u (P.charts.chart D.center y,t)
  rw [←D.inverse_chart theta hy]
  exact patchTransportCLM_inverse_value hg N Ccut hCcut hN h2rho hCut hTime hr
    hgamma0 hgamma1 D htheta u (P.charts.chart D.center y,t)

/-- Applying the inverse-Hessian operator to the genuinely transported element
recovers the original Levi matrix at the actual forward coordinate. -/
theorem patchTransportCLM_inverse_levi (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    c1 D theta z (gradientFun (Transport u) ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun (Transport u) ⟨D.center,(z,t)⟩)=
      leviC (chartFunction u D.center t) (cutoffTranslation D.bump theta z) := by
  rw [inverseLeviFromStoredJet D htheta]
  apply L22Aux.leviC_congr_of_eventuallyEq
  have hzSource : (z : ComplexVector n)∈(P.charts.chart D.center).source :=
    P.charts.closedBall_source D.center
      (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hThetaSource := D.coordinate_forward_mem_source htheta hzSource
  filter_upwards [(P.charts.chart D.center).open_source.mem_nhds hThetaSource] with y hy
  exact patchTransportCLM_inverseChart hg N Ccut hCcut hN h2rho hCut hTime hr
    hgamma0 hgamma1 D htheta u t hy

end Yau.LeafProofs.L17BootstrapTransportAux
