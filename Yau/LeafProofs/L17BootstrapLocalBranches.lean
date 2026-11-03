import Yau.LeafProofs.L17BootstrapCandidateBranch
import Yau.LeafProofs.L17BootstrapConcreteIFTInputs
import Yau.LeafProofs.L17BootstrapBranchIdentification

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapLocalBranchesAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17BootstrapPatchAux
open L17BootstrapPositiveBaseHolderAux L17LocalHolderBanachAlgebraAux
open L17BootstrapInverseHessianCoefficientsAux L17BootstrapTransportAux
open L17BootstrapBackgroundDifferenceAux L17LocalizedSchauderAux
open L17BootstrapConcreteIFTInputsAux L17BootstrapConcreteCoefficientsAux
open L17BootstrapBranchIdentificationAux L17BootstrapMetricAux
local instance actualLocalBranchesMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T : ℝ} {hT : 0<T}

/-- The fixed original base solution has genuine smooth spatial translation
branches at every point, on the same full closed time interval. -/
theorem exists_actual_local_shift_branches
    (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
    (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (J : LocalHolderSpace ℝ P T (1/4) →L[ℝ] HolderSpace P T (1/4))
    (hJ : ∀ w, holderFun (J w)=L17LocalScalarAssemblyAux.scalarAssemblyFunction P w)
    (ua : SchauderSpace P T (1/2) hT) (ub : SchauderSpace P T (1/4) hT)
    (hFun : schauderFun ua=schauderFun ub)
    (hubZ : ‖normalizedMetricPerturbation P T (1/4) hT hTime (by norm_num) (by norm_num) hr ub‖<1)
    (hubSmall : ‖ub‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hubEq : scalarParabolicCLM P T (1/4) hT hTime (by norm_num) hr ub=
      globalNonlinearMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J ub)
    (B0 : SchauderSpace P T (1/4) hT ≃L[ℝ] HolderSpace P T (1/4))
    (hB0 : B0.toContinuousLinearMap=fderiv ℝ
      (scalarNonlinearResidualMap P T (1/4) hT hTime (by norm_num) (by norm_num) hr J) ub) :
    ∀x : M.Carrier,∃D : BootstrapPatch P x,∃r : ℝ,
      0<r ∧ r≤D.smallRadius/2 ∧
      ∃V : ComplexVector n → SchauderSpace P T (1/4) hT,
        ContDiffOn ℝ ∞ V (ball 0 r) ∧
        ∀theta∈ball 0 r,∀t : Time T,
          schauderFun (V theta) (x,t)=schauderFun ub (P.charts.chart D.center (D.coord+theta),t) := by
  intro x
  obtain ⟨D⟩ := exists_bootstrapPatch P x
  obtain ⟨H,K,G,U,V,W,hG0,hG,hH,hK,hU,hU0,hUsub,hW,hW0,hWsub,hV,hV0,hEq,hUnique,hSmall⟩ :=
    exists_concrete_parameter_branch D h2rho hT hTime (by norm_num) (by norm_num) hr
      J ub hubZ hubSmall hubEq B0 hB0
  have hC0 : ∀theta∈ball 0 (D.smallRadius/2),∀q : LocalCylinder P T,
      c0Hat (beta := (1/4 : ℝ)) D h2rho hT hTime (by norm_num) (by norm_num) hr theta q=
        shiftedBackgroundValue D theta q := by
    intro theta htheta q
    simpa only [shiftedBackgroundValue] using
      c0Hat_value (beta := (1/4 : ℝ)) D h2rho hT hTime (by norm_num) (by norm_num) hr htheta q
  have hWtheta : ∀a∈W,a.1∈ball 0 (D.smallRadius/2) := fun a ha => hUsub (hWsub ha).1
  have hCandidate : ∀theta,‖theta‖<D.smallRadius →
      (theta,patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta)∈W →
      G (theta,patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta)=0 := by
    intro theta htheta hvW
    exact actual_parameter_candidate_zero hg N Ccut hCcut hN h2rho hCut hTime hr D J hJ
      ub hubZ hubSmall hubEq K (c0Hat (beta := (1/4 : ℝ)) D h2rho hT hTime (by norm_num) (by norm_num) hr)
      H G W hC0 hH hK hG hWtheta hSmall htheta _ rfl hvW
  obtain ⟨r,hrPos,hrSmall,_,hVr,_,hShift⟩ := actual_transport_branch_identification hg N Ccut
    hCcut hN h2rho hCut hTime hr D ua ub hFun G U V W hU hU0 hW hW0 hV hV0 hUnique hCandidate
  exact ⟨D,r,hrPos,hrSmall,V,hVr,hShift⟩

end Yau.LeafProofs.L17BootstrapLocalBranchesAux
