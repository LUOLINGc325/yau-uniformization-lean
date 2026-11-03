import Yau.LeafProofs.L17BootstrapTransportLocalScaledJets
import Yau.LeafProofs.L17BootstrapTransportTrueJets
import Yau.LeafProofs.L17LocalizedSchauderUniformAssembly

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def assemblyBudget (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (Ccut gamma : ℝ) (hCcut : 0 ≤ Ccut) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) : ℝ :=
  Classical.choose (exists_uniform_localized_schauder_assembly A hg N Ccut gamma hCcut hgamma0 hgamma1)

theorem assemblyBudget_pos (A : BoundedChartFamily g) (hg : MetricSmooth g)
    (N : ℕ) (Ccut gamma : ℝ) (hCcut : 0 ≤ Ccut) (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    0 < assemblyBudget A hg N Ccut gamma hCcut hgamma0 hgamma1 :=
  (Classical.choose_spec (exists_uniform_localized_schauder_assembly A hg N Ccut gamma hCcut hgamma0 hgamma1)).1

variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}
variable (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0 ≤ Ccut)
variable (hN : P.overlapBudget ≤ N) (h2rho : 2*P.radius < P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)

include hN h2rho hCut hTime hr htheta

theorem exists_unique_correction_element (u : SchauderSpace P T gamma hT) :
    ∃! w : SchauderSpace P T gamma hT,
      schauderFun w=globalSum P T (correctionFamily D theta u) ∧
      ‖w‖ ≤ assemblyBudget P.charts hg N Ccut gamma hCcut hgamma0 hgamma1*
        (2*(transportBudget D*‖u‖)) := by
  have hSpec := (Classical.choose_spec (exists_uniform_localized_schauder_assembly
    P.charts hg N Ccut gamma hCcut hgamma0 hgamma1)).2
  exact hSpec P rfl hN hr h2rho hCut T hT (2*(transportBudget D*‖u‖))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (transportBudget_pos D).le (norm_nonneg u)))
    (correctionFamily D theta u) (correctionGradientFamily D theta u)
    (correctionHessianFamily D theta u) (correctionTimeFamily D theta u)
    (correctionFamily_localTrueJets D htheta u)
    (correctionFamily_localScaledJetBounds D htheta hgamma0.le hgamma1 hTime hr u)

def correctionElement (u : SchauderSpace P T gamma hT) : SchauderSpace P T gamma hT :=
  Classical.choose (exists_unique_correction_element hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u).exists

theorem correctionElement_spec (u : SchauderSpace P T gamma hT) :
    schauderFun (correctionElement hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u)=
        globalSum P T (correctionFamily D theta u) ∧
    ‖correctionElement hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u‖ ≤
      assemblyBudget P.charts hg N Ccut gamma hCcut hgamma0 hgamma1*(2*(transportBudget D*‖u‖)) :=
  Classical.choose_spec (exists_unique_correction_element hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u).exists

theorem correctionElement_norm_le (u : SchauderSpace P T gamma hT) :
    ‖correctionElement hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u‖ ≤
      (assemblyBudget P.charts hg N Ccut gamma hCcut hgamma0 hgamma1*(2*transportBudget D))*‖u‖ := by
  exact (correctionElement_spec hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u).2.trans_eq (by ring)

end Yau.LeafProofs.L17BootstrapTransportAux
