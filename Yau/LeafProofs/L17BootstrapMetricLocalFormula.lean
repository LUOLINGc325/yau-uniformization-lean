import Yau.LeafProofs.L17BootstrapInverseHessianCoefficients
import Yau.LeafProofs.L17BootstrapMetricCoefficients

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17SmallTranslationAux
open L17ParabolicOperatorAux
open L17BootstrapInverseHessianCoefficientsAux
local instance metricLocalFormulaMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)
include htheta

/-- The real stored jets produce the actual inverse-coordinate Levi matrix.
The first-derivative contribution is retained. -/
theorem inverseLeviFromStoredJet (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    c1 D theta z (gradientFun u ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun u ⟨D.center,(z,t)⟩)=
      leviC (fun y => chartFunction u D.center t
        (cutoffInverse D.bump D.bump_smooth D.bound
          (zero_le_one.trans D.bound_ge_one) D.derivative_bound theta y))
        (cutoffTranslation D.bump theta z) := by
  have h1 := (chartFunction_hasFDerivAt u D.center t z.property).fderiv
  have h2 := (chartFunction_hasSecondFDerivAt u D.center t z.property).fderiv
  rw [←h1,←h2,add_comm]
  exact inverseComposition_levi D htheta z (chartFunction u D.center t)
    ((chartFunction_contDiffOn_two u D.center t).contDiffAt
      (isOpen_ball.mem_nhds z.property))

theorem inverseLeviFromStoredJet_isHermitian (u : SchauderSpace P T gamma hT)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    (c1 D theta z (gradientFun u ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun u ⟨D.center,(z,t)⟩)).IsHermitian := by
  rw [inverseLeviFromStoredJet D htheta]
  exact L22Aux.leviC_isHermitian (inverseComposition_contDiffAt_two D htheta z
    (chartFunction u D.center t)
    ((chartFunction_contDiffOn_two u D.center t).contDiffAt
      (isOpen_ball.mem_nhds z.property)))

end Yau.LeafProofs.L17BootstrapMetricAux
