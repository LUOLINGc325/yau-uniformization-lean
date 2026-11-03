import Yau.LeafProofs.L17BootstrapPatchHomeomorph

open Set Metric Filter
open scoped Topology ContDiff Manifold Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapPatchAux
open L17Aux L17SmallTranslationAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier}
namespace BootstrapPatch
variable (D : BootstrapPatch P x)

theorem forward_joint_contMDiffAt {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (y : M.Carrier) :
    ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n) ∞
      (fun p : ComplexVector n × M.Carrier => D.forward p.1 p.2) (θ,y) := by
  let _patchForwardAtProofRealSmooth := L12Aux.manifold_realSmooth M
  let e := P.charts.chart D.center
  by_cases hy : y ∈ e.target
  · have hInverse : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
        ∞ e.symm y :=
      ((inverse_chart_real_contMDiffOn e (P.charts.inverse_differentiable D.center)) y hy).contMDiffAt
        (e.open_target.mem_nhds hy)
    have hPair : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
        𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
        (fun p : ComplexVector n × M.Carrier => (p.1,e.symm p.2)) (θ,y) :=
      contMDiffAt_fst.prodMk_space (hInverse.comp (θ,y) contMDiffAt_snd)
    have hTheta := (cutoffTranslation_joint_contDiff D.bump_smooth).comp_contMDiffAt hPair
    have hSource := D.coordinate_forward_mem_source hθ (e.symm.map_source hy)
    have hChart := ((chart_real_contMDiffOn e (P.charts.differentiable D.center))
      (cutoffTranslation D.bump θ (e.symm y)) hSource).contMDiffAt
        (e.open_source.mem_nhds hSource)
    have hComp := hChart.comp (θ,y) hTheta
    apply hComp.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (e.open_target.mem_nhds hy)] with p hp
    exact D.forward_of_mem_target p.1 hp
  · have hK : y ∉ D.supportSet := fun h => hy (D.supportSet_subset_target h)
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually
      (D.supportSet_isCompact.isClosed.isOpen_compl.mem_nhds hK)] with p hp
    exact D.forward_eq_self_of_not_mem_support p.1 hp

theorem inverse_joint_contMDiffAt {θ : ComplexVector n} (hθ : ‖θ‖ < D.smallRadius)
    (y : M.Carrier) :
    ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n) ∞
      (fun p : ComplexVector n × M.Carrier => D.inverse p.1 p.2) (θ,y) := by
  let _patchInverseAtProofRealSmooth := L12Aux.manifold_realSmooth M
  let e := P.charts.chart D.center
  by_cases hy : y ∈ e.target
  · have hInverse : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n)
        ∞ e.symm y :=
      ((inverse_chart_real_contMDiffOn e (P.charts.inverse_differentiable D.center)) y hy).contMDiffAt
        (e.open_target.mem_nhds hy)
    have hPair : ContMDiffAt (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
        𝓘(ℝ, ComplexVector n × ComplexVector n) ∞
        (fun p : ComplexVector n × M.Carrier => (p.1,e.symm p.2)) (θ,y) :=
      contMDiffAt_fst.prodMk_space (hInverse.comp (θ,y) contMDiffAt_snd)
    have hPsi := (cutoffInverse_joint_contDiffAt D.bump D.bump_smooth D.bound
      (zero_le_one.trans D.bound_ge_one) D.derivative_bound
        (hθ.trans_le D.smallRadius_le_translation) (e.symm y)).comp_contMDiffAt
          (f := fun p : ComplexVector n × M.Carrier => (p.1,e.symm p.2)) (x := (θ,y)) hPair
    have hSource := D.coordinate_inverse_mem_source hθ (e.symm.map_source hy)
    have hChart := ((chart_real_contMDiffOn e (P.charts.differentiable D.center))
      (cutoffInverse D.bump D.bump_smooth D.bound (zero_le_one.trans D.bound_ge_one)
        D.derivative_bound θ (e.symm y)) hSource).contMDiffAt
          (e.open_source.mem_nhds hSource)
    have hComp := hChart.comp (θ,y) hPsi
    apply hComp.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (e.open_target.mem_nhds hy)] with p hp
    exact D.inverse_of_mem_target p.1 hp
  · have hK : y ∉ D.supportSet := fun h => hy (D.supportSet_subset_target h)
    have hBall : θ ∈ ball (0 : ComplexVector n) D.smallRadius :=
      by simpa only [mem_ball,dist_zero_right] using hθ
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (isOpen_ball.mem_nhds hBall),
      continuousAt_snd.eventually
        (D.supportSet_isCompact.isClosed.isOpen_compl.mem_nhds hK)] with p hpθ hp
    exact D.inverse_eq_self_of_not_mem_support
      (by simpa only [mem_ball,dist_zero_right] using hpθ) hp

theorem forward_joint_contMDiffOn :
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n) ∞
      (fun p : ComplexVector n × M.Carrier => D.forward p.1 p.2)
      (ball (0 : ComplexVector n) D.smallRadius ×ˢ (univ : Set M.Carrier)) := by
  let _patchForwardOnProofRealSmooth := L12Aux.manifold_realSmooth M
  intro p hp
  exact (D.forward_joint_contMDiffAt
    (by simpa only [mem_ball,dist_zero_right] using hp.1) p.2).contMDiffWithinAt

theorem inverse_joint_contMDiffOn :
    ContMDiffOn (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n) ∞
      (fun p : ComplexVector n × M.Carrier => D.inverse p.1 p.2)
      (ball (0 : ComplexVector n) D.smallRadius ×ˢ (univ : Set M.Carrier)) := by
  let _patchInverseOnProofRealSmooth := L12Aux.manifold_realSmooth M
  intro p hp
  exact (D.inverse_joint_contMDiffAt
    (by simpa only [mem_ball,dist_zero_right] using hp.1) p.2).contMDiffWithinAt

end BootstrapPatch
end Yau.LeafProofs.L17BootstrapPatchAux
