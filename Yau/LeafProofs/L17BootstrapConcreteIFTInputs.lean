import Yau.LeafProofs.L17BootstrapParameterBranch
import Yau.LeafProofs.L17BootstrapConcreteCoefficients

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapConcreteIFTInputsAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapPositiveBaseHolderAux
open L17BootstrapMetricAux L17BootstrapBackgroundDifferenceAux L17BootstrapConcreteCoefficientsAux
open L17BootstrapInverseHessianCoefficientsAux
local instance concreteIFTInputsMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (h2rho : 2*P.radius<P.charts.radius)
  (hT : 0<T) (hTime : T≤P.radius^2) (hb0 : 0<beta) (hb1 : beta<1) (hr : P.radius≤1)
local notation "X" => SchauderSpace P T beta hT
local notation "Y" => HolderSpace P T beta
local notation "BMat" => LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta
local notation "Phi" => scalarNonlinearResidualMap P T beta hT hTime hb0.le hb1.le hr
local notation "Hbase" => Hstar P hT hTime hb0.le hb1.le hr
local notation "Zbg" => normalizedMetricPerturbation P T beta hT hTime hb0.le hb1.le hr
local notation "Bkg" => backgroundDifferences D h2rho hT hTime hb0 hb1
local notation "c0" => c0Hat D h2rho hT hTime hb0 hb1 hr

/-- Bind the actual background coefficients to the parameter IFT at the same
chosen base solution. The source neighborhood also fixes its parameter domain. -/
theorem exists_concrete_parameter_branch
    (J : LocalHolderSpace ℝ P T beta →L[ℝ] Y)
    (ub : X) (hubZ : ‖Zbg ub‖<1)
    (hubSmall : ‖ub‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hubEq : scalarParabolicCLM P T beta hT hTime hb1.le hr ub=
      globalNonlinearMap P T beta hT hTime hb0.le hb1.le hr J ub)
    (B0 : X ≃L[ℝ] Y) (hB0 : B0.toContinuousLinearMap=fderiv ℝ (Phi J) ub) :
    ∃ H : ComplexVector n × X → BMat, ∃ K : BMat, ∃ G : ComplexVector n × X → Y,
      ∃ U : Set (ComplexVector n), ∃ V : ComplexVector n → X, ∃ W : Set (ComplexVector n × X),
      (∀ v, G (0,v)=Phi J v) ∧
      (∀ a, G a=Phi J a.2-assembledLogCorrection P T beta J (Bkg).sigma K (Hbase ub)
        (H a) (Hbase a.2) ((Bkg).logHat a.1)) ∧
      (∀ theta∈ball 0 (D.smallRadius/2), ∀ u, ∀ q : LocalCylinder P T,
        H (theta,u) q=c0 theta q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun u q)+
          c2Family D theta q.1 q.2.1 q.2.2 (hessianFun u q)) ∧
      (∀ q : LocalCylinder P T, K q=(Hbase ub q)⁻¹) ∧
      IsOpen U ∧ (0 : ComplexVector n)∈U ∧ U⊆ball 0 (D.smallRadius/2) ∧
      IsOpen W ∧ (0,ub)∈W ∧ W⊆U ×ˢ univ ∧ ContDiffOn ℝ ∞ V U ∧ V 0=ub ∧
      (∀ theta∈U, (theta,V theta)∈W ∧ G (theta,V theta)=0) ∧
      (∀ theta∈U, ∀ v, (theta,v)∈W → G (theta,v)=0 → v=V theta) ∧
      ∀ a∈W,
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (H a)‖<1 ∧
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (Hbase a.2)‖<1 ∧
        ‖Zbg a.2‖<1 ∧ (∀ q : LocalCylinder P T, (Hbase a.2 q).PosDef) := by
  obtain ⟨H,K,G,U,V,W0,hG0,hFormula,hHval,hK,hU,hU0,hUsub,hW0,hWbase,hV,hVbase,
      hEq,hUnique,hSmall⟩ :=
    exists_conjugated_parameter_branch D hT hTime hb0 hb1 hr J (Bkg).sigma c0
      (c0Hat_contDiffOn D h2rho hT hTime hb0 hb1 hr)
      (c0Hat_zero D h2rho hT hTime hb0 hb1 hr)
      (Bkg).logHat (Bkg).log_contDiff (Bkg).log_zero ub hubZ hubSmall hubEq B0 hB0
  let W := W0 ∩ (U ×ˢ univ)
  refine ⟨H,K,G,U,V,W,hG0,hFormula,hHval,hK,hU,hU0,hUsub,
    hW0.inter (hU.prod isOpen_univ),⟨hWbase,hU0,mem_univ ub⟩,
    inter_subset_right,hV,hVbase,?_,?_,?_⟩
  · intro theta htheta
    obtain ⟨hMem,hZero⟩ := hEq theta htheta
    exact ⟨⟨hMem,htheta,mem_univ _⟩,hZero⟩
  · intro theta htheta v hv hZero
    exact hUnique theta htheta v hv.1 hZero
  · intro a ha
    exact hSmall a ha.1

end Yau.LeafProofs.L17BootstrapConcreteIFTInputsAux
