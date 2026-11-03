import Yau.LeafProofs.L17BootstrapInverseHessianHolder
import Yau.LeafProofs.L17BootstrapMetricBase
import Yau.LeafProofs.L17BootstrapMetricLocalFormula

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapPositiveBaseHolderAux
open L17BootstrapInverseHessianCoefficientsAux L17BootstrapInverseHessianHolderAux
local instance shiftedMetricMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (hT : 0<T) (hTime : T≤P.radius^2)
  (hb0 : 0<beta) (hb1 : beta<1) (hr : P.radius≤1)

/-- The actual inverse-Hessian Holder coefficients assemble a jointly smooth metric map.
The sole background input is the already constructed coefficient family c0. -/
theorem exists_shifted_metric_family
    (c0 : ComplexVector n → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta)
    (hc0 : ContDiffOn ℝ ∞ c0 (ball 0 (D.smallRadius/2)))
    (hc00 : c0 0=Hstar P hT hTime hb0.le hb1.le hr 0) :
    ∃ H : ComplexVector n × SchauderSpace P T beta hT →
        LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta,
      ContDiffOn ℝ ∞ H (ball 0 (D.smallRadius/2) ×ˢ univ) ∧
      (∀ u, H (0,u)=Hstar P hT hTime hb0.le hb1.le hr u) ∧
      ∀ theta∈ball 0 (D.smallRadius/2), ∀ u, ∀ q : LocalCylinder P T,
        H (theta,u) q=c0 theta q+
          c1Family D theta q.1 q.2.1 q.2.2 (gradientFun u q)+
          c2Family D theta q.1 q.2.1 q.2.2 (hessianFun u q) := by
  obtain ⟨C1,C2,hC1,hC2,hVal1,hVal2,hC10,hC20,_⟩ :=
    exists_inverse_hessian_banach_lifts D hT hTime hb0 hb1
  let H : ComplexVector n × SchauderSpace P T beta hT →
      LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta := fun a =>
    metricFromCoefficients P T beta hT (c0 a.1) (C1 a.1) (C2 a.1) a.2
  refine ⟨H,?_,?_,?_⟩
  · exact metricFromCoefficients_contDiffOn P T beta hT
      (hc0.comp contDiff_fst.contDiffOn (fun _ ha => ha.1))
      (hC1.comp contDiff_fst.contDiffOn (fun _ ha => ha.1))
      (hC2.comp contDiff_fst.contDiffOn (fun _ ha => ha.1))
      contDiff_snd.contDiffOn
  · intro u
    change metricFromCoefficients P T beta hT (c0 0) (C1 0) (C2 0) u=_
    rw [hc00,hC10,hC20]
    exact metricFromCoefficients_unshifted P hT hTime hb0.le hb1.le hr u
  · intro theta htheta u q
    change metricFromCoefficients P T beta hT (c0 theta) (C1 theta) (C2 theta) u q=_
    rw [metricFromCoefficients_value]
    change c0 theta q+localFun (FirstCoefficient n) (C1 theta).value q (gradientFun u q)+
      localFun (SecondCoefficient n) (C2 theta).value q (hessianFun u q)=_
    rw [hVal1 theta htheta q,hVal2 theta htheta q]

end Yau.LeafProofs.L17BootstrapMetricAux
