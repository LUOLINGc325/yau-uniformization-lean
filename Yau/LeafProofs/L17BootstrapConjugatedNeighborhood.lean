import Yau.LeafProofs.L17BootstrapShiftedMetric
import Yau.LeafProofs.L17BootstrapConjugatedResidual
import Yau.LeafProofs.L17BootstrapMetricDomain

noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexOrder
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapMetricAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17LocalHolderBanachAlgebraAux L17BootstrapPositiveBaseHolderAux
open L17BootstrapInverseHessianCoefficientsAux
local instance conjugatedNeighborhoodMatrixTopology (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) := leviMatrixTopology n
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T beta : ℝ} (hT : 0<T) (hTime : T≤P.radius^2)
  (hb0 : 0<beta) (hb1 : beta<1) (hr : P.radius≤1)
local notation "X" => SchauderSpace P T beta hT
local notation "BMat" => LocalHolderBanach (Matrix (Fin n) (Fin n) ℂ) P T beta
local notation "Phi" => scalarNonlinearResidualMap P T beta hT hTime hb0.le hb1.le hr
local notation "Hbase" => Hstar P hT hTime hb0.le hb1.le hr
local notation "Zbg" => normalizedMetricPerturbation P T beta hT hTime hb0.le hb1.le hr

/-- Build the actual parameter-dependent residual on one open analytic neighborhood
of the positive base. All inverse-Hessian coefficients and the base inverse are
obtained from the proved constructions, rather than supplied as inverse data. -/
theorem exists_conjugated_residual_neighborhood
    (J : LocalHolderSpace ℝ P T beta →L[ℝ] HolderSpace P T beta)
    (sigma : LocalHolderSpace ℝ P T beta)
    (c0 : ComplexVector n → BMat)
    (hc0 : ContDiffOn ℝ ∞ c0 (ball 0 (D.smallRadius/2)))
    (hc00 : c0 0=Hbase 0)
    (dLog : ComplexVector n → LocalHolderSpace ℝ P T beta)
    (hdLog : ContDiffOn ℝ ∞ dLog (ball 0 (D.smallRadius/2))) (hdLog0 : dLog 0=0)
    (ub : X) (hubZ : ‖Zbg ub‖<1)
    (hubSmall : ‖ub‖+T*backgroundLogDetHessianBudget P.charts≤(P.charts.bound 0)⁻¹) :
    ∃ H : ComplexVector n × X → BMat, ∃ K : BMat,
      ∃ Omega : Set (ComplexVector n × X),
        ∃ G : ComplexVector n × X → HolderSpace P T beta,
      IsOpen Omega ∧ (0,ub)∈Omega ∧ ContDiffOn ℝ ∞ G Omega ∧
      (∀ v, G (0,v)=Phi J v) ∧
      (∀ a, G a=Phi J a.2-assembledLogCorrection P T beta J sigma K (Hbase ub)
        (H a) (Hbase a.2) (dLog a.1)) ∧
      (∀ theta∈ball 0 (D.smallRadius/2), ∀ u, ∀ q : LocalCylinder P T,
        H (theta,u) q=c0 theta q+c1Family D theta q.1 q.2.1 q.2.2 (gradientFun u q)+
          c2Family D theta q.1 q.2.1 q.2.2 (hessianFun u q)) ∧
      (∀ q : LocalCylinder P T, K q=(Hbase ub q)⁻¹) ∧
      ∀ a∈Omega,
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (H a)‖<1 ∧
        ‖relativeMetricPerturbation P T beta K (Hbase ub) (Hbase a.2)‖<1 ∧
        ‖Zbg a.2‖<1 ∧ (∀ q : LocalCylinder P T, (Hbase a.2 q).PosDef) := by
  obtain ⟨H,hH,hHzero,hHval⟩ := exists_shifted_metric_family D hT hTime hb0 hb1 hr c0 hc0 hc00
  obtain ⟨K,B,hB,hK,hLeft,hRight,hKnorm⟩ :=
    exists_Hstar_inverse P hT hTime hb0.le hb1.le hr ub hubSmall
  let S : Set (ComplexVector n × X) := ball 0 (D.smallRadius/2) ×ˢ univ
  let V0 : Set (ComplexVector n × X) := {a | ‖Zbg a.2‖<1}
  let H0 : ComplexVector n × X → BMat := fun a => Hbase a.2
  let Omega := metricDomain P T beta S V0 K (Hbase ub) (baseLambda P) H H0
  let G : ComplexVector n × X → HolderSpace P T beta := fun a =>
    Phi J a.2-assembledLogCorrection P T beta J sigma K (Hbase ub) (H a) (H0 a) (dLog a.1)
  have hS : IsOpen S := isOpen_ball.prod isOpen_univ
  have hV0 : IsOpen V0 :=
    (scalarNonlinearResidual_domain_isOpen P T beta hT hTime hb0.le hb1.le hr).preimage continuous_snd
  have hH0 : ContDiff ℝ ∞ H0 :=
    (Hstar_contDiff P hT hTime hb0.le hb1.le hr).comp contDiff_snd
  have hOmega : IsOpen Omega :=
    metricDomain_isOpen P T beta hS hV0 K (Hbase ub) (baseLambda P) hH hH0.contDiffOn
  have hBase : (0,ub)∈Omega := by
    exact mem_metricDomain_base P T beta (s := S) (V0 := V0)
      (Htheta := H) (Hzero := H0) (a := (0,ub)) K (Hbase ub) (baseLambda_pos P)
      ⟨by simpa only [mem_ball,dist_self] using half_pos D.smallRadius_pos,mem_univ _⟩
      hubZ (hHzero ub) rfl
  have hSubset : Omega⊆S := fun a ha => ha.1.1.1
  have hSmall (a) (ha : a∈Omega) :
      ‖relativeMetricPerturbation P T beta K (Hbase ub) (H a)‖<1 ∧
      ‖relativeMetricPerturbation P T beta K (Hbase ub) (H0 a)‖<1 := by
    obtain ⟨ht,h0⟩ := metricDomain_relative_norms P T beta K (Hbase ub) (baseLambda P) ha
    exact ⟨ht.trans (by norm_num),h0.trans (by norm_num)⟩
  have hSmoothLog : ContDiffOn ℝ ∞
      (fun a => assembledLogCorrection P T beta J sigma K (Hbase ub) (H a) (H0 a) (dLog a.1))
        Omega :=
    assembledLogCorrection_contDiffOn P T beta J sigma K (Hbase ub)
      (hH.mono hSubset) hH0.contDiffOn
      (hdLog.comp contDiff_fst.contDiffOn (fun a ha => (hSubset ha).1))
      (fun a ha => (hSmall a ha).1) (fun a ha => (hSmall a ha).2)
  have hSmoothPhi : ContDiffOn ℝ ∞ (fun a : ComplexVector n × X => Phi J a.2) Omega :=
    (scalarNonlinearResidualMap_contDiffOn P T beta hT hTime hb0.le hb1.le hr J).comp
      contDiff_snd.contDiffOn (fun a ha => ha.2)
  refine ⟨H,K,Omega,G,hOmega,hBase,hSmoothPhi.sub hSmoothLog,?_,?_,hHval,hK,?_⟩
  · intro v
    change Phi J v-assembledLogCorrection P T beta J sigma K (Hbase ub)
      (H (0,v)) (Hbase v) (dLog 0)=Phi J v
    rw [hHzero v,hdLog0,assembledLogCorrection_zero,sub_zero]
  · intro a
    rfl
  · intro a ha
    refine ⟨(hSmall a ha).1,(hSmall a ha).2,ha.2,?_⟩
    intro q
    exact local_metric_posDef_of_norm_close P T beta (Hbase ub) (Hbase a.2)
      (baseLambda_pos P) (Hstar_uniform_lower P hT hTime hb0.le hb1.le hr ub hubSmall)
      (Hstar_isHermitian P hT hTime hb0.le hb1.le hr a.2)
      (ha.1.2.le.trans (min_le_left _ _)) q

end Yau.LeafProofs.L17BootstrapMetricAux
