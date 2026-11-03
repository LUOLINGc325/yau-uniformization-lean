import Yau.LeafProofs.L17BootstrapCandidatePath

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
local instance candidateBranchMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T : ℝ} {hT : 0<T}

/-- All hypotheses are literal outputs of the concrete IFT and original N8
base. The actual transported element is a zero of that very same G. -/
theorem actual_parameter_candidate_zero
    (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
    (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (D : BootstrapPatch P x)
    (J : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4))
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (u : SchauderSpace P T (1/4) hT)
    (huZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr u‖<1)
    (huSmall : ‖u‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hEquation : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr u=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J u)
    (K : LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T (1/4))
    (c0 : ComplexVector n → LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T (1/4))
    (H : ComplexVector n × SchauderSpace P T (1/4) hT →
      LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T (1/4))
    (G : ComplexVector n × SchauderSpace P T (1/4) hT → HolderSpace P T (1/4))
    (W : Set (ComplexVector n × SchauderSpace P T (1/4) hT))
    (hC0 : ∀theta∈ball 0 (D.smallRadius/2),∀q : LocalCylinder P T,
      c0 theta q=shiftedBackgroundValue D theta q)
    (hH : ∀theta∈ball 0 (D.smallRadius/2),∀v,∀q : LocalCylinder P T,
      H (theta,v) q=c0 theta q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun v q)+
        c2Family D theta q.1 q.2.1 q.2.2 (hessianFun v q))
    (hK : ∀q : LocalCylinder P T, K q=(Hstar P hT hTime (by norm_num) (by norm_num) hr u q)⁻¹)
    (hG : ∀a, G a=scalarNonlinearResidualMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J a.2-
      assembledLogCorrection P T (1/4) J
        (backgroundDifferences D h2rho hT hTime (by norm_num) (by norm_num)).sigma K
        (Hstar P hT hTime (by norm_num) (by norm_num) hr u) (H a)
        (Hstar P hT hTime (by norm_num) (by norm_num) hr a.2)
        ((backgroundDifferences D h2rho hT hTime (by norm_num) (by norm_num)).logHat a.1))
    (hWtheta : ∀a∈W,a.1∈ball 0 (D.smallRadius/2))
    (hSmall : ∀a∈W,
      ‖relativeMetricPerturbation P T (1/4) K (Hstar P hT hTime (by norm_num) (by norm_num) hr u) (H a)‖<1 ∧
      ‖relativeMetricPerturbation P T (1/4) K (Hstar P hT hTime (by norm_num) (by norm_num) hr u)
        (Hstar P hT hTime (by norm_num) (by norm_num) hr a.2)‖<1 ∧
      ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr a.2‖<1 ∧
      ∀q : LocalCylinder P T,(Hstar P hT hTime (by norm_num) (by norm_num) hr a.2 q).PosDef)
    {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)
    (v : SchauderSpace P T (1/4) hT)
    (hvPath : v=patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D u theta)
    (hvW : (theta,v)∈W) : G (theta,v)=0 := by
  obtain ⟨hSmallt,hSmall0,hvZ,hvPos⟩ := hSmall (theta,v) hvW
  have huPos := Hstar_posDef P hT hTime (by norm_num) (by norm_num) hr u huSmall
  have hthetaR := hWtheta (theta,v) hvW
  rw [hG]
  exact conjugatedResidual_zero_of_patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr
    D htheta hthetaR J hJ u v hvPath huZ hvZ huPos hvPos hEquation K (H (theta,v))
    (fun q => c0 theta q) (hC0 theta hthetaR) (hH theta hthetaR v) hK hSmallt hSmall0

end Yau.LeafProofs.L17BootstrapMetricAux
