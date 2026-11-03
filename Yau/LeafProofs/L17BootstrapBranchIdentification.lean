import Yau.LeafProofs.L17BootstrapTransport

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapBranchIdentificationAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux L17BootstrapTransportAux L17LocalizedSchauderAux
attribute [local instance] transportLinearSchauderGroup transportLinearSchauderNormedSpace transportLinearSchauderModule

/-- Actual alpha-to-beta transport continuity and IFT uniqueness select one
parameter ball for the entire closed time interval and every derivative order. -/
theorem actual_transport_branch_identification
    {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    {P : UniformChartPartition g} {x : M.Carrier} {T : ℝ} {hT : 0<T}
    (hg : MetricSmooth g) (N : ℕ) (Ccut : ℝ) (hCcut : 0≤Ccut)
    (hN : P.overlapBudget≤N) (h2rho : 2*P.radius<P.charts.radius)
    (hCut : CutoffJetBounds P 2 Ccut) (hTime : T≤P.radius^2) (hr : P.radius≤1)
    (D : BootstrapPatch P x)
    (ua : SchauderSpace P T (1/2) hT) (ub : SchauderSpace P T (1/4) hT)
    (hFun : schauderFun ua=schauderFun ub)
    (G : ComplexVector n × SchauderSpace P T (1/4) hT → HolderSpace P T (1/4))
    (U : Set (ComplexVector n)) (V : ComplexVector n → SchauderSpace P T (1/4) hT)
    (W : Set (ComplexVector n × SchauderSpace P T (1/4) hT))
    (hU : IsOpen U) (hU0 : (0 : ComplexVector n)∈U)
    (hW : IsOpen W) (hW0 : ((0 : ComplexVector n),ub)∈W)
    (hV : ContDiffOn ℝ ∞ V U) (_hV0 : V 0=ub)
    (hUnique : ∀ theta∈U, ∀ v, (theta,v)∈W → G (theta,v)=0 → v=V theta)
    (hCandidate : ∀ theta, ‖theta‖<D.smallRadius →
      (theta,patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta)∈W →
      G (theta,patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta)=0) :
    ∃ delta : ℝ, 0<delta ∧ delta≤D.smallRadius/2 ∧
      ball (0 : ComplexVector n) delta⊆U ∧
      ContDiffOn ℝ ∞ V (ball (0 : ComplexVector n) delta) ∧
      (∀ theta∈ball (0 : ComplexVector n) delta,
        (theta,patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta)∈W ∧
        V theta=patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub theta) ∧
      (∀ theta∈ball (0 : ComplexVector n) delta, ∀ t : Time T,
        schauderFun (V theta) (x,t)=
          schauderFun ub (P.charts.chart D.center (D.coord+theta),t)) := by
  let path := patchTransportPath hg N Ccut hCcut hN h2rho hCut hTime hr D ub
  have hPath : ContinuousAt path 0 :=
    patchTransportPath_continuousAt_zero hg N Ccut hCcut hN h2rho hCut hTime hr D ua ub hFun
  have hPath0 : path 0=ub := patchTransportPath_zero hg N Ccut hCcut hN h2rho hCut hTime hr D ub
  have hGraph : ContinuousAt (fun theta => (theta,path theta)) 0 := continuousAt_id.prodMk hPath
  have hWNear : W∈𝓝 ((0 : ComplexVector n),path 0) := by
    rw [hPath0]
    exact hW.mem_nhds hW0
  have hNear : {theta : ComplexVector n | (theta,path theta)∈W}∈𝓝 0 :=
    hGraph.preimage_mem_nhds hWNear
  obtain ⟨epsilon,hepsilon,hBall⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hU0) hNear)
  let delta := min epsilon (D.smallRadius/2)
  have hdelta : 0<delta := lt_min hepsilon (half_pos D.smallRadius_pos)
  have hDeltaBound : delta≤D.smallRadius/2 := min_le_right _ _
  have hInto : ball (0 : ComplexVector n) delta⊆U∩{theta | (theta,path theta)∈W} :=
    (ball_subset_ball (min_le_left _ _)).trans hBall
  have hSmall (theta) (htheta : theta∈ball (0 : ComplexVector n) delta) : ‖theta‖<D.smallRadius := by
    have hNorm : ‖theta‖<delta := by simpa only [mem_ball,dist_zero_right] using htheta
    exact (hNorm.trans_le hDeltaBound).trans (half_lt_self D.smallRadius_pos)
  have hIdent (theta) (htheta : theta∈ball (0 : ComplexVector n) delta) :
      (theta,path theta)∈W ∧ V theta=path theta := by
    have hm := hInto htheta
    exact ⟨hm.2,(hUnique theta hm.1 (path theta) hm.2 (hCandidate theta (hSmall theta htheta) hm.2)).symm⟩
  refine ⟨delta,hdelta,hDeltaBound,(fun _ h => (hInto h).1),
    hV.mono (fun _ h => (hInto h).1),hIdent,?_⟩
  intro theta htheta t
  rw [(hIdent theta htheta).2]
  exact (patchTransportPath_value hg N Ccut hCcut hN h2rho hCut hTime hr D ub
    (hSmall theta htheta) (x,t)).trans (congrArg (fun y => schauderFun ub (y,t))
      (D.forward_center_translation theta))

end Yau.LeafProofs.L17BootstrapBranchIdentificationAux
