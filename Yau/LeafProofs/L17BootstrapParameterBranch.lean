import Yau.LeafProofs.L17BootstrapConjugatedNeighborhood
import Yau.LeafProofs.L17BanachImplicitFunction

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapPositiveBaseHolderAux
open L17BootstrapInverseHessianCoefficientsAux L17BanachImplicitFunctionAux
local instance parameterBranchMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (hT : 0<T) (hTime : T≤P.radius^2)
  (hb0 : 0<beta) (hb1 : beta<1) (hr : P.radius≤1)
local notation "X" => SchauderSpace P T beta hT
local notation "Y" => HolderSpace P T beta
local notation "BMat" => LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta
local notation "Phi" => scalarNonlinearResidualMap P T beta hT hTime hb0.le hb1.le hr
local notation "Hbase" => Hstar P hT hTime hb0.le hb1.le hr
local notation "Zbg" => normalizedMetricPerturbation P T beta hT hTime hb0.le hb1.le hr

/-- Instantiate the parameter IFT with the actual residual and its actual base
linearization, on one common parameter neighborhood and the original time interval. -/
theorem exists_conjugated_parameter_branch
    (J : LocalHolderSpace ℝ P T beta →L[ℝ] Y) (sigma : LocalHolderSpace ℝ P T beta)
    (c0 : ComplexVector n → BMat)
    (hc0 : ContDiffOn ℝ ∞ c0 (ball 0 (D.smallRadius/2))) (hc00 : c0 0=Hbase 0)
    (dLog : ComplexVector n → LocalHolderSpace ℝ P T beta)
    (hdLog : ContDiffOn ℝ ∞ dLog (ball 0 (D.smallRadius/2))) (hdLog0 : dLog 0=0)
    (ub : X) (hubZ : ‖Zbg ub‖<1)
    (hubSmall : ‖ub‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹)
    (hubEq : scalarParabolicCLM P T beta hT hTime hb1.le hr ub=
      globalNonlinearMap P T beta hT hTime hb0.le hb1.le hr J ub)
    (B0 : X ≃L[ℝ] Y) (hB0 : B0.toContinuousLinearMap=fderiv ℝ (Phi J) ub) :
    ∃ H : ComplexVector n × X → BMat, ∃ K : BMat, ∃ G : ComplexVector n × X → Y,
      ∃ U : Set (ComplexVector n), ∃ V : ComplexVector n → X, ∃ W : Set (ComplexVector n × X),
      (∀ v, G (0,v)=Phi J v) ∧
      (∀ a, G a=Phi J a.2-assembledLogCorrection P T beta J sigma K (Hbase ub)
        (H a) (Hbase a.2) (dLog a.1)) ∧
      (∀ theta∈ball 0 (D.smallRadius/2), ∀ u, ∀ q : LocalCylinder P T,
        H (theta,u) q=c0 theta q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun u q)+
          c2Family D theta q.1 q.2.1 q.2.2 (hessianFun u q)) ∧
      (∀ q : LocalCylinder P T, K q=(Hbase ub q)⁻¹) ∧
      IsOpen U ∧ (0 : ComplexVector n)∈U ∧ U⊆ball 0 (D.smallRadius/2) ∧
      IsOpen W ∧ (0,ub)∈W ∧ ContDiffOn ℝ ∞ V U ∧ V 0=ub ∧
      (∀ theta∈U, (theta,V theta)∈W ∧ G (theta,V theta)=0) ∧
      (∀ theta∈U, ∀ v, (theta,v)∈W → G (theta,v)=0 → v=V theta) ∧
      ∀ a∈W,
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (H a)‖<1 ∧
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (Hbase a.2)‖<1 ∧
        ‖Zbg a.2‖<1 ∧ (∀ q : LocalCylinder P T, (Hbase a.2 q).PosDef) := by
  obtain ⟨H,K,Omega,G,hOmega,hBase,hG,hG0,hFormula,hHval,hK,hSmall⟩ :=
    exists_conjugated_residual_neighborhood D hT hTime hb0 hb1 hr J sigma c0 hc0 hc00
      dLog hdLog hdLog0 ub hubZ hubSmall
  have hGBase : G (0,ub)=0 := by
    rw [hG0,scalarNonlinearResidualMap,hubEq,sub_self]
  have hPhiD : HasFDerivAt (Phi J) (B0 : X →L[ℝ] Y) ub := by
    rw [hB0]
    exact (scalarNonlinearResidualMap_hasFDerivAt P T beta hT hTime hb0.le hb1.le hr J hubZ).differentiableAt.hasFDerivAt
  have hSlice : HasFDerivAt (fun v => G (0,v)) (B0 : X →L[ℝ] Y) ub := by
    rw [show (fun v => G (0,v))=Phi J from funext hG0]
    exact hPhiD
  obtain ⟨U,V,W,hU,hU0,hW,hW0,hWsub,hV,hV0,hEq,hUnique⟩ :=
    implicit_function_of_slice_derivative hOmega hG ub hBase hGBase B0 hSlice
  have hZero : (0 : ComplexVector n)∈ball 0 (D.smallRadius/2) := by
    simpa only [mem_ball,dist_self] using half_pos D.smallRadius_pos
  refine ⟨H,K,G,U∩ball 0 (D.smallRadius/2),V,W,hG0,hFormula,hHval,hK,
    hU.inter isOpen_ball,⟨hU0,hZero⟩,inter_subset_right,hW,hW0,hV.mono inter_subset_left,hV0,?_,?_,?_⟩
  · intro theta htheta
    exact hEq theta htheta.1
  · intro theta htheta v hv hZeroG
    exact hUnique theta htheta.1 v hv hZeroG
  · intro a ha
    exact hSmall a (hWsub ha)

end Yau.LeafProofs.L17BootstrapMetricAux
