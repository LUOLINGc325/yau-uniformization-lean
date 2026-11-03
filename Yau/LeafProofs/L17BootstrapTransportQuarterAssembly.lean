import Yau.LeafProofs.L17BootstrapTransportLinearMap

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
attribute [local instance] transportLinearSchauderGroup transportLinearSchauderNormedSpace transportLinearSchauderModule
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T : ℝ} {hT : 0 < T}
variable (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0 ≤ Ccut)
variable (hN : P.overlapBudget ≤ N) (h2rho : 2*P.radius < P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)

def quarterAssemblyBudget : ℝ :=
  assemblyBudget P.charts hg N Ccut (1/4) hCcut (by norm_num) (by norm_num)

include hN h2rho hCut hTime hr htheta

theorem exists_unique_quarter_correction (u : SchauderSpace P T (1/2) hT) :
    ∃! w : SchauderSpace P T (1/4) hT,
      schauderFun w=globalSum P T (correctionFamily D theta u) ∧
      ‖w‖ ≤ quarterAssemblyBudget (P := P) hg N Ccut hCcut*
        (2*(4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ))) := by
  have hSpec := (Classical.choose_spec (exists_uniform_localized_schauder_assembly P.charts hg
    N Ccut (1/4) hCcut (by norm_num) (by norm_num))).2
  have hF : 0 ≤ 2*(4*(transportBudget D*‖u‖)*(‖theta‖/P.radius)^(1/4 : ℝ)) := by
    have hb := (transportBudget_pos D).le
    have heps := Real.rpow_nonneg (BootstrapPatch.parameter_fraction_nonneg (P := P) theta) (1/4 : ℝ)
    positivity
  exact hSpec P rfl hN hr h2rho hCut T hT _ hF
    (correctionFamily D theta u) (correctionGradientFamily D theta u)
    (correctionHessianFamily D theta u) (correctionTimeFamily D theta u)
    (correctionFamily_localTrueJets D htheta u)
    (correctionFamily_quarterScaledJetBounds D htheta hTime hr u)

def quarterCorrectionElement (u : SchauderSpace P T (1/2) hT) : SchauderSpace P T (1/4) hT :=
  Classical.choose (exists_unique_quarter_correction hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u).exists

theorem quarterCorrectionElement_value (u : SchauderSpace P T (1/2) hT) (q : Cylinder M T) :
    schauderFun (quarterCorrectionElement hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u) q=
      schauderFun u (D.forward theta q.1,q.2)-schauderFun u q := by
  have h : schauderFun (quarterCorrectionElement hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u)=
      globalSum P T (correctionFamily D theta u) := (Classical.choose_spec
    (exists_unique_quarter_correction hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u).exists).1
  rw [h]
  exact globalSum_correctionFamily_value D theta u q

theorem quarterCorrectionElement_norm_le (u : SchauderSpace P T (1/2) hT) :
    ‖quarterCorrectionElement hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u‖ ≤
      4*quarterAssemblyBudget (P := P) hg N Ccut hCcut*(2*transportBudget D)*‖u‖*(‖theta‖/P.radius)^(1/4 : ℝ) := by
  have h := (Classical.choose_spec
    (exists_unique_quarter_correction hg N Ccut hCcut hN h2rho hCut hTime hr D htheta u).exists).2
  exact h.trans_eq (by ring)

theorem correctionCLM_eq_quarter_of_function_eq (ua : SchauderSpace P T (1/2) hT)
    (ub : SchauderSpace P T (1/4) hT) (hFun : schauderFun ua=schauderFun ub) :
    correctionCLM hg N Ccut hCcut hN h2rho hCut hTime hr (by norm_num) (by norm_num) D htheta ub=
      quarterCorrectionElement hg N Ccut hCcut hN h2rho hCut hTime hr D htheta ua := by
  apply schauderFun_injective
  funext q
  rw [correctionCLM_value,quarterCorrectionElement_value,hFun]

theorem patchTransport_quarter_difference_norm_le (ua : SchauderSpace P T (1/2) hT)
    (ub : SchauderSpace P T (1/4) hT) (hFun : schauderFun ua=schauderFun ub) :
    ‖patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr (by norm_num) (by norm_num) D htheta ub-ub‖ ≤
      4*quarterAssemblyBudget (P := P) hg N Ccut hCcut*(2*transportBudget D)*‖ua‖*(‖theta‖/P.radius)^(1/4 : ℝ) := by
  change ‖ub+correctionCLM hg N Ccut hCcut hN h2rho hCut hTime hr
    (by norm_num) (by norm_num) D htheta ub-ub‖ ≤ _
  rw [add_sub_cancel_left,correctionCLM_eq_quarter_of_function_eq hg N Ccut hCcut hN h2rho hCut hTime hr D htheta ua ub hFun]
  exact quarterCorrectionElement_norm_le hg N Ccut hCcut hN h2rho hCut hTime hr D htheta ua

end Yau.LeafProofs.L17BootstrapTransportAux
