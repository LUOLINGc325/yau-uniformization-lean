import Yau.LeafProofs.L17BootstrapTransport

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17LocalizedSchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} {T gamma : ℝ} {hT : 0<T}
variable (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
  (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
  (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
  (hgamma0 : 0<gamma) (hgamma1 : gamma≤1)
  (D : BootstrapPatch P x) {theta : ComplexVector n} (htheta : ‖theta‖<D.smallRadius)

/-- The genuine transported Banach element has the actual transported time derivative
at every time, including both endpoints of the original slab. -/
theorem patchTransportCLM_timeFun (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    timeFun (patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u) q=
      timeFun u (D.forward theta q.1,q.2) := by
  let w := patchTransportCLM hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u
  have hEq : (fun tau => schauderFun w (closedTimePath T hT q.1 tau))=
      (fun tau => schauderFun u (closedTimePath T hT (D.forward theta q.1) tau)) := by
    funext tau
    exact patchTransportCLM_value hg N Ccut hCcut hN h2rho hCut hTime hr hgamma0 hgamma1 D htheta u _
  have hW := schauderFun_hasDerivWithinAt w q.1 q.2
  rw [hEq] at hW
  exact (hW.derivWithin (uniqueDiffOn_Icc hT (q.2 : ℝ) q.2.property)).symm.trans
    ((schauderFun_hasDerivWithinAt u (D.forward theta q.1) q.2).derivWithin
      (uniqueDiffOn_Icc hT (q.2 : ℝ) q.2.property))

end Yau.LeafProofs.L17BootstrapTransportAux
