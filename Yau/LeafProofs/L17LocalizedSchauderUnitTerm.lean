import Yau.LeafProofs.L17LocalizedSchauderDistance
import Yau.LeafProofs.L17LocalizedSchauderScaledNearCover

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def unitCutoff (P : UniformChartPartition g) (p : P.centers) (q : M.Carrier) (z : ComplexVector n) : ℝ :=
  P.localization p (P.charts.chart q (P.radius • z))

def unitLocalizedTerm (P : UniformChartPartition g) (T : ℝ) (p : P.centers) (q : M.Carrier)
    (v : ComplexVector n × Time T → ℝ) (t : Time T) : ComplexVector n → ℝ :=
  unitValue P.radius (fun z => localizedTerm P T p v (P.charts.chart q z,t))

theorem unitLocalizedTerm_eq_product (P : UniformChartPartition g) (T : ℝ)
    (hρone : P.radius ≤ 1) (p : P.centers) (q : M.Carrier)
    (v : ComplexVector n × Time T → ℝ) (t : Time T) :
    let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
    unitLocalizedTerm P T p q v t =
      (fun z => unitCutoff P p q z*unitValue P.radius (fun w => v (w,t)) (P.charts.scaledTransitionMap a z)) := by
  funext z
  simp only [unitLocalizedTerm,unitValue,unitCutoff,localizedTerm,
    BoundedChartFamily.scaledTransitionMap,BoundedChartFamily.transitionMap,
    smul_smul,mul_inv_cancel₀ P.radius_pos.ne',one_smul,smul_eq_mul]
  ring

theorem unitCutoff_contDiffOn (P : UniformChartPartition g) (hρr : 2*P.radius < P.charts.radius)
    (p : P.centers) (q : M.Carrier) :
    ContDiffOn ℝ ∞ (unitCutoff P p q) (ball (0 : ComplexVector n) 2) :=
  smoothFn_comp_scaledChart_contDiffOn P.charts (P.localization_smooth p) P.radius_pos hρr q

theorem unitLocalizedTerm_contDiffAt_two (P : UniformChartPartition g) (T : ℝ)
    (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ) (t : Time T)
    (hv : ContDiffOn ℝ 2 (fun z => v (z,t)) (ball (0 : ComplexVector n) (2*P.radius)))
    {z : ComplexVector n} (hz : z ∈ ball 0 1) :
    ContDiffAt ℝ 2 (unitLocalizedTerm P T p q v t) z := by
  have hzρ : P.radius • z ∈ ball (0 : ComplexVector n) P.radius := by
    apply mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [mul_one] using mul_lt_mul_of_pos_left hn P.radius_pos
  have hRaw := localizedTerm_chart_contDiffAt_two P T p q v t hv hzρ
  have hScale : ContDiffAt ℝ 2 (fun w : ComplexVector n => P.radius • w) z :=
    (P.radius • ContinuousLinearMap.id ℝ (ComplexVector n)).contDiff.contDiffAt
  exact (ContDiffAt.comp z hRaw hScale).const_smul ((P.radius^2)⁻¹)

theorem unitLocalizedTerm_zero_neighborhood (P : UniformChartPartition g) (T : ℝ)
    (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ)
    {z : ComplexVector n} (hz : z ∈ ball 0 1)
    (hx : P.charts.chart q (P.radius • z) ∉ P.charts.chart p '' closedBall 0 P.radius) :
    ∀ᶠ w in 𝓝 z, ∀ t : Time T, unitLocalizedTerm P T p q v t w = 0 := by
  have hzρ : P.radius • z ∈ ball (0 : ComplexVector n) P.radius := by
    apply mem_ball.mpr
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
    have hn : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [mul_one] using mul_lt_mul_of_pos_left hn P.radius_pos
  have hSource := P.charts.closedBall_source q
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hzρ))
  have hChart : ContinuousAt (P.charts.chart q) (P.radius • z) :=
    (P.charts.chart q).continuousOn.continuousAt ((P.charts.chart q).open_source.mem_nhds hSource)
  have hScale : ContinuousAt (fun w : ComplexVector n => P.radius • w) z := by fun_prop
  have hMap : ContinuousAt (fun w : ComplexVector n => P.charts.chart q (P.radius • w)) z :=
    hChart.comp hScale
  filter_upwards [hMap.eventually (localizedTerm_zero_neighborhood P T p v hx)] with w hw t
  change (P.radius^2)⁻¹ • localizedTerm P T p v (P.charts.chart q (P.radius • w),t) = 0
  rw [hw t,smul_zero]

theorem unitLocalizedTerm_iteratedFDeriv_zero (P : UniformChartPartition g) (T : ℝ)
    (p : P.centers) (q : M.Carrier) (v : ComplexVector n × Time T → ℝ) (t : Time T)
    {z : ComplexVector n} (hz : z ∈ ball 0 1)
    (hx : P.charts.chart q (P.radius • z) ∉ P.charts.chart p '' closedBall 0 P.radius) (k : ℕ) :
    iteratedFDeriv ℝ k (unitLocalizedTerm P T p q v t) z = 0 := by
  have heq : unitLocalizedTerm P T p q v t =ᶠ[𝓝 z] (fun _ => 0) :=
    (unitLocalizedTerm_zero_neighborhood P T p q v hz hx).mono (fun w hw => hw t)
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds,iteratedFDeriv_zero_function]

end Yau.LeafProofs.L17LocalizedSchauderAux
