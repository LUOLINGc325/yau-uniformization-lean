import Yau.LeafProofs.L17LocalScalarAssemblyBasic

open Set Metric Filter
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem weightedLocalFunction_continuous_on_chart (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) :
    Continuous (fun q : ChartCylinder P T => weightedLocalFunction P u p (q.1,q.2)) := by
  have hu : Continuous (fun q : ChartCylinder P T => localFun ℝ u ⟨p,q⟩) :=
    u.val.1.continuous.comp continuous_sigmaMk
  have hw : Continuous (fun q : ChartCylinder P T => P.weight p (P.charts.chart p q.1)) :=
    ((L18Aux.contMDiff_real_of_smoothFn (P.weight_smooth p)).continuous.comp continuous_fst).comp
      (chartPoint_continuous P T p)
  convert hw.mul hu using 1
  funext q
  simp only [weightedLocalFunction,dite_eq_left q.1.property,Pi.mul_apply]

theorem weightedLocalFunction_continuous (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) : Continuous (weightedLocalFunction P u p) := by
  have hOn : ContinuousOn (weightedLocalFunction P u p)
      (ball (0 : ComplexVector n) P.radius ×ˢ (Set.univ : Set (Time T))) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let c : ↥(ball (0 : ComplexVector n) P.radius ×ˢ (Set.univ : Set (Time T))) → ChartCylinder P T :=
      fun q => (⟨q.1.1,q.2.1⟩,q.1.2)
    have hc : Continuous c :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun q => q.2.1)).prodMk
        (continuous_snd.comp continuous_subtype_val)
    convert (weightedLocalFunction_continuous_on_chart P u p).comp hc using 1
    funext q
    rfl
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hz : q.1 ∈ ball (0 : ComplexVector n) P.radius
  · exact hOn.continuousAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hz,mem_univ _⟩)
  · have hhalf : q.1 ∉ closedBall (0 : ComplexVector n) (P.radius/2) := fun hh =>
      hz ((closedBall_subset_ball (by linarith [P.radius_pos])) hh)
    have hEq : weightedLocalFunction P u p =ᶠ[𝓝 q] (fun _ => 0) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        (isClosed_closedBall.isOpen_compl.mem_nhds hhalf)] with r hr
      exact weightedLocalFunction_zero_outside_half P u p hr r.2
    exact continuousAt_const.congr_of_eventuallyEq hEq

end Yau.LeafProofs.L17LocalScalarAssemblyAux
