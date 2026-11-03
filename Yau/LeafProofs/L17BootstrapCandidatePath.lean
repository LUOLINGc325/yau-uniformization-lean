import Yau.LeafProofs.L17BootstrapCandidateZero
import Yau.LeafProofs.L17BootstrapTransportInverse
import Yau.LeafProofs.L17BootstrapBackgroundDifference

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17BootstrapPatchAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux
open L17BootstrapInverseHessianCoefficientsAux L17BootstrapTransportAux
open L17BootstrapBackgroundDifferenceAux L17LocalizedSchauderAux
local instance candidatePathMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T : ℝ} {hT : 0<T}

/-- All candidate value, time, inverse-Hessian and background-log identities
are supplied by the actual transport and actual coefficient providers. -/
theorem conjugatedResidual_zero_of_patchTransportPath
    (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
    (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (D : BootstrapPatch P x) {theta : ComplexVector n}
    (htheta : ‖theta‖<D.smallRadius) (hthetaR : theta∈ball 0 (D.smallRadius/2))
    (J : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4))
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u v : SchauderSpace P T (1/4) hT)
    (hvPath : v=patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D u theta)
    (huZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr u‖<1)
    (hvZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr v‖<1)
    (huPos : ∀q : LocalCylinder P T, (Hstar P hT hTime (by norm_num) (by norm_num) hr u q).PosDef)
    (hvPos : ∀q : LocalCylinder P T, (Hstar P hT hTime (by norm_num) (by norm_num) hr v q).PosDef)
    (hEquation : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr u=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J u)
    (K H : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T (1/4))
    (c0 : LocalCylinder P T → Matrix (Fin n) (Fin n) ℂ)
    (hC0 : ∀q, c0 q=shiftedBackgroundValue D theta q)
    (hH : ∀q, H q=c0 q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
      c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (hK : ∀q : LocalCylinder P T, K q=(Hstar P hT hTime (by norm_num) (by norm_num) hr u q)⁻¹)
    (hSmallt : ‖relativeMetricPerturbation P T (1/4) K
      (Hstar P hT hTime (by norm_num) (by norm_num) hr u) H‖<1)
    (hSmall0 : ‖relativeMetricPerturbation P T (1/4) K
      (Hstar P hT hTime (by norm_num) (by norm_num) hr u)
      (Hstar P hT hTime (by norm_num) (by norm_num) hr v)‖<1) :
    scalarNonlinearResidualMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J v-
      assembledLogCorrection P T (1/4) J
        (backgroundDifferences D h2rho hT hTime (by norm_num) (by norm_num)).sigma K
        (Hstar P hT hTime (by norm_num) (by norm_num) hr u) H
        (Hstar P hT hTime (by norm_num) (by norm_num) hr v)
        ((backgroundDifferences D h2rho hT hTime (by norm_num) (by norm_num)).logHat theta)=0 := by
  let B := backgroundDifferences D h2rho hT hTime (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1/4:ℝ)<1)
  have hValue (y : M.Carrier) (t : Time T) :
      schauderFun v (y,t)=schauderFun u (D.forward theta y,t) := by
    rw [hvPath]
    exact patchTransportPath_value hg N Ccut hCcut hN h2rho hCut hTime hr D u htheta (y,t)
  have hTimeValue (q : Cylinder M T) : timeFun v q=timeFun u (D.forward theta q.1,q.2) := by
    rw [hvPath,patchTransportPath_of_small hg N Ccut hCcut hN h2rho hCut hTime hr D u htheta]
    exact patchTransportCLM_timeFun hg N Ccut hCcut hN h2rho hCut hTime hr
      (by norm_num) (by norm_num) D htheta u q
  have hInverse (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
      c1 D theta z (gradientFun v ⟨D.center,(z,t)⟩)+
      c2 D theta z (hessianFun v ⟨D.center,(z,t)⟩)=
        leviC (chartFunction u D.center t) (L17SmallTranslationAux.cutoffTranslation D.bump theta z) := by
    rw [hvPath,patchTransportPath_of_small hg N Ccut hCcut hN h2rho hCut hTime hr D u htheta]
    exact patchTransportCLM_inverse_levi hg N Ccut hCcut hN h2rho hCut hTime hr
      (by norm_num) (by norm_num) D htheta u z t
  apply conjugatedResidual_zero_of_transport_values D htheta hg hTime (by norm_num) (by norm_num) hr
    J hJ u v huZ hvZ huPos hvPos hEquation hValue hTimeValue hInverse K H c0
    (B.logHat theta) B.sigma hC0 hH hK hSmallt hSmall0
  · intro z t
    simpa [logFamily,logSpecial,BoundedChartFamily.backgroundLogDet]
      using B.log_value theta hthetaR ⟨D.center,(z,t)⟩
  · exact B.log_collar theta hthetaR
  · intro q
    simpa only [sigmaFamily,normalizationSpecial] using B.sigma_value q
  · intro z hz
    exact weight_normalization_cancel D hz

end Yau.LeafProofs.L17BootstrapMetricAux
