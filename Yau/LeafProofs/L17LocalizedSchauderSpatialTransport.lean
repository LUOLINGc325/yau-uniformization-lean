import Yau.LeafProofs.L17LocalizedSchauderTwoJets
import Yau.LeafProofs.L17BackgroundFunctionSmooth

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- The transported local scalar is genuinely C² in every selected chart;
outside its actual cutoff cover it is a zero germ. -/
theorem localizedTerm_chart_contDiffAt_two (P : UniformChartPartition g) (T : ℝ)
    (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ) (t : Time T)
    (hv : ContDiffOn ℝ 2 (fun z => v (z,t)) (ball (0 : ComplexVector n) (2*P.radius)))
    {z : ComplexVector n} (hz : z ∈ ball 0 P.radius) :
    ContDiffAt ℝ 2 (fun w => localizedTerm P T p v (P.charts.chart q w,t)) z := by
  have hzr : z ∈ ball (0 : ComplexVector n) P.charts.radius := (ball_subset_ball P.radius_lt.le) hz
  have hzSource := P.charts.closedBall_source q (ball_subset_closedBall hzr)
  have hCutoff : ContDiffAt ℝ 2 (fun w => P.localization p (P.charts.chart q w)) z :=
    ((smoothFn_comp_backgroundChart_contDiffOn P.charts (P.localization_smooth p) q).contDiffAt
      (isOpen_ball.mem_nhds hzr)).of_le (by simp)
  by_cases hx : P.charts.chart q z ∈ P.charts.chart p '' closedBall 0 P.radius
  · obtain ⟨hTarget,hInverse⟩ := inverseChart_mem_of_cover P p hx
    have hInverseBall : (P.charts.chart p).symm (P.charts.chart q z) ∈ ball (0 : ComplexVector n) (2*P.radius) :=
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hInverse) (by have := P.radius_pos; linarith))
    have hDomain : z ∈ transitionDomain (P.charts.chart q) (P.charts.chart p) := ⟨hzSource,hTarget⟩
    have hTransition : ContDiffAt ℝ 2 (fun w => (P.charts.chart p).symm (P.charts.chart q w)) z :=
      ((transition_real_contDiffOn (P.charts.chart q) (P.charts.chart p)
        (P.charts.differentiable q) (P.charts.inverse_differentiable p)).contDiffAt
          ((transitionDomain_isOpen _ _).mem_nhds hDomain)).of_le (by simp)
    have hV : ContDiffAt ℝ 2 (fun w => v (w,t)) ((P.charts.chart p).symm (P.charts.chart q z)) :=
      hv.contDiffAt (isOpen_ball.mem_nhds hInverseBall)
    have hComp : ContDiffAt ℝ 2
        (fun w => v ((P.charts.chart p).symm (P.charts.chart q w),t)) z :=
      ContDiffAt.comp (g := fun w : ComplexVector n => v (w,t))
        (f := fun w => (P.charts.chart p).symm (P.charts.chart q w)) z hV hTransition
    exact hCutoff.mul hComp
  · have hChart : ContinuousAt (P.charts.chart q) z :=
      (P.charts.chart q).continuousOn.continuousAt ((P.charts.chart q).open_source.mem_nhds hzSource)
    have hZero : (fun w => localizedTerm P T p v (P.charts.chart q w,t)) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hChart.eventually (localizedTerm_zero_neighborhood P T p v hx)] with w hw
      exact hw t
    exact contDiffAt_const.congr_of_eventuallyEq hZero

theorem localizedTerm_chart_contDiffOn_two (P : UniformChartPartition g) (T : ℝ)
    (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ) (t : Time T)
    (hv : ContDiffOn ℝ 2 (fun z => v (z,t)) (ball (0 : ComplexVector n) (2*P.radius))) :
    ContDiffOn ℝ 2 (fun w => localizedTerm P T p v (P.charts.chart q w,t)) (ball 0 P.radius) :=
  fun z hz => (localizedTerm_chart_contDiffAt_two P T p q v t hv hz).contDiffWithinAt

end Yau.LeafProofs.L17LocalizedSchauderAux
