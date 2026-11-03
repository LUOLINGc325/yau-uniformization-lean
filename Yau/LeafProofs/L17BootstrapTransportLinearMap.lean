import Yau.LeafProofs.L17BootstrapTransportAssembly
import Yau.LeafProofs.L17BootstrapTransportLiteralSum

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0 < T}

local instance transportLinearSchauderGroup (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T) :
    NormedAddCommGroup (SchauderSpace P T gamma hT) := schauderSpace_normedAddCommGroup P T gamma hT
local instance transportLinearSchauderNormedSpace (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T) :
    NormedSpace ℝ (SchauderSpace P T gamma hT) := schauderSpace_normedSpace P T gamma hT

local instance transportLinearSchauderModule (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0<T) :
    Module ℝ (SchauderSpace P T gamma hT) := (schauderSpace_normedSpace P T gamma hT).toModule

theorem schauderFun_add_value (u v : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (u+v) q=schauderFun u q+schauderFun v q := by
  change (functionCLM P T gamma hT (u+v)) q=(functionCLM P T gamma hT u) q+(functionCLM P T gamma hT v) q
  rw [(functionCLM P T gamma hT).map_add u v]
  rfl

theorem schauderFun_smul_value (c : ℝ) (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (c • u : SchauderSpace P T gamma hT) q=c*schauderFun u q := by
  change (functionCLM P T gamma hT (c • u : SchauderSpace P T gamma hT)) q=c*(functionCLM P T gamma hT u) q
  rw [(functionCLM P T gamma hT).map_smul c u]
  rfl

variable (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0 ≤ Ccut)
variable (hN : P.overlapBudget ≤ N) (h2rho : 2*P.radius < P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T ≤ P.radius^2) (hr : P.radius ≤ 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
variable (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius)

local notation "CE" => correctionElement hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta
local notation "C0" => assemblyBudget P.charts hg N Ccut gamma hCcut hgamma0 hgamma1

theorem correctionElement_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (CE u) q=schauderFun u (D.forward theta q.1,q.2)-schauderFun u q := by
  rw [(correctionElement_spec hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u).1]
  exact globalSum_correctionFamily_value D theta u q

def correctionLinearMap : SchauderSpace P T gamma hT →ₗ[ℝ] SchauderSpace P T gamma hT where
  toFun := CE
  map_add' u v := by
    apply schauderFun_injective
    funext q
    simp only [correctionElement_value,schauderFun_add_value]
    abel
  map_smul' c u := by
    apply schauderFun_injective
    funext q
    simp only [correctionElement_value,schauderFun_smul_value,RingHom.id_apply]
    ring

def correctionCLM : SchauderSpace P T gamma hT →L[ℝ] SchauderSpace P T gamma hT :=
  (correctionLinearMap hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta).mkContinuous
    (C0*(2*transportBudget D)) (by
      intro u
      change ‖CE u‖ ≤ _
      exact correctionElement_norm_le hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u)

theorem correctionCLM_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (correctionCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u) q=
      schauderFun u (D.forward theta q.1,q.2)-schauderFun u q :=
  correctionElement_value hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u q

theorem correctionCLM_opNorm_le :
    ‖correctionCLM (hT := hT) hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta‖ ≤ C0*(2*transportBudget D) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (assemblyBudget_pos P.charts hg N Ccut gamma hCcut hgamma0 hgamma1).le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (transportBudget_pos D).le))
  intro u
  exact correctionElement_norm_le hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u

def patchTransportCLM : SchauderSpace P T gamma hT →L[ℝ] SchauderSpace P T gamma hT :=
  ContinuousLinearMap.id ℝ (SchauderSpace P T gamma hT)+
    correctionCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta

theorem patchTransportCLM_value (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderFun (patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u) q=
      schauderFun u (D.forward theta q.1,q.2) := by
  change schauderFun (u+CE u) q=_
  rw [schauderFun_add_value,correctionElement_value]
  ring

theorem patchTransportCLM_opNorm_le :
    ‖patchTransportCLM (hT := hT) hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta‖ ≤
      1+C0*(2*transportBudget D) := by
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := SchauderSpace P T gamma hT))
    (correctionCLM_opNorm_le hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta))

end Yau.LeafProofs.L17BootstrapTransportAux
