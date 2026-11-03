import Yau.LeafProofs.L17BootstrapTransportQuarterAssembly

open Set Metric Filter
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
variable (D : BootstrapPatch P x)

def patchTransportPath (ub : SchauderSpace P T (1/4) hT) (theta : ComplexVector n) :
    SchauderSpace P T (1/4) hT :=
  if htheta : ‖theta‖ < D.smallRadius then
    patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr
      (by norm_num) (by norm_num) D htheta ub else ub

theorem patchTransportPath_of_small (ub : SchauderSpace P T (1/4) hT)
    {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius) :
    patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta=
      patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr
        (by norm_num) (by norm_num) D htheta ub := dite_eq_left htheta

theorem patchTransportPath_value (ub : SchauderSpace P T (1/4) hT)
    {theta : ComplexVector n} (htheta : ‖theta‖ < D.smallRadius) (q : Cylinder M T) :
    schauderFun (patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta) q=
      schauderFun ub (D.forward theta q.1,q.2) := by
  rw [patchTransportPath_of_small hg N Ccut hCcut hN h2rho hCut hTime hr D ub htheta]
  exact patchTransportCLM_value hg N Ccut hCcut hN h2rho hCut hTime hr
    (by norm_num) (by norm_num) D htheta ub q

theorem patchTransportPath_zero (ub : SchauderSpace P T (1/4) hT) :
    patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub 0=ub := by
  have h0 : ‖(0 : ComplexVector n)‖ < D.smallRadius := by simpa only [norm_zero] using D.smallRadius_pos
  apply schauderFun_injective
  funext q
  rw [patchTransportPath_value hg N Ccut hCcut hN h2rho hCut hTime hr D ub h0,D.forward_zero_parameter]

theorem patchTransportPath_continuousAt_zero (ua : SchauderSpace P T (1/2) hT)
    (ub : SchauderSpace P T (1/4) hT) (hFun : schauderFun ua=schauderFun ub) :
    ContinuousAt (patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub) 0 := by
  change Tendsto (patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub)
    (𝓝 0) (𝓝 (patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub 0))
  rw [patchTransportPath_zero hg N Ccut hCcut hN h2rho hCut hTime hr D ub,
    tendsto_iff_norm_sub_tendsto_zero]
  let K := 4*quarterAssemblyBudget (P := P) hg N Ccut hCcut*(2*transportBudget D)*‖ua‖
  have hPower : ContinuousAt (fun theta : ComplexVector n => K*(‖theta‖/P.radius)^(1/4 : ℝ)) 0 :=
    continuousAt_const.mul (((continuous_norm.div_const P.radius).continuousAt).rpow_const
      (Or.inr (by norm_num : (0 : ℝ) ≤ 1/4)))
  have hLimit : Tendsto (fun theta : ComplexVector n => K*(‖theta‖/P.radius)^(1/4 : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero,zero_div,Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0),mul_zero] using hPower.tendsto
  have hSmall : ∀ᶠ theta : ComplexVector n in 𝓝 0, ‖theta‖ < D.smallRadius := by
    have h0 : (0 : ComplexVector n) ∈ ball (0 : ComplexVector n) D.smallRadius := by
      simpa only [mem_ball,dist_self] using D.smallRadius_pos
    filter_upwards [isOpen_ball.mem_nhds h0] with theta htheta
    simpa only [mem_ball,dist_zero_right] using htheta
  have hBound : ∀ᶠ theta : ComplexVector n in 𝓝 0,
      ‖patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta-ub‖ ≤
        K*(‖theta‖/P.radius)^(1/4 : ℝ) := by
    filter_upwards [hSmall] with theta htheta
    rw [patchTransportPath_of_small hg N Ccut hCcut hN h2rho hCut hTime hr D ub htheta]
    exact patchTransport_quarter_difference_norm_le hg N Ccut hCcut hN h2rho hCut hTime hr D htheta ua ub hFun
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hBound hLimit

end Yau.LeafProofs.L17BootstrapTransportAux
