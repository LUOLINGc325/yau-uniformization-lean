import Yau.LeafProofs.L17UniformPartitionBudget

/-! Real scalar regularity in the actual background and rescaled charts. -/

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem smoothFn_comp_backgroundChart_contDiffOn
    (A : BoundedChartFamily g) {f : M.Carrier → ℝ} (hf : SmoothFn f) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => f (A.chart p z)) (ball 0 A.radius) := by
  let := L12Aux.manifold_realSmooth M
  have h := (L18Aux.contMDiff_real_of_smoothFn hf).comp_contMDiffOn
    (chart_real_contMDiffOn (A.chart p) (A.differentiable p))
  rw [contMDiffOn_iff_contDiffOn] at h
  exact h.mono (fun _ hz => A.closedBall_source p (ball_subset_closedBall hz))

theorem smoothFn_comp_scaledChart_contDiffOn
    (A : BoundedChartFamily g) {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : 2 * ρ < A.radius) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => f (A.chart p (ρ • z))) (ball (0 : ComplexVector n) 2) := by
  have hL : ContDiff ℝ ∞ (fun z : ComplexVector n => ρ • z) := by
    convert! (ρ • ContinuousLinearMap.id ℝ (ComplexVector n)).contDiff using 1
  apply (smoothFn_comp_backgroundChart_contDiffOn A hf p).comp hL.contDiffOn
  intro z hz
  have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball, dist_zero_right] using hz
  apply mem_ball.mpr
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  nlinarith

theorem UniformChartPartition.chartWeightSum_smoothFn (P : UniformChartPartition g) :
    SmoothFn (chartWeightSum P.charts P.centers P.radius P.radius_pos) :=
  L18Aux.smoothFn_of_contMDiff_real
    (P.charts.chartWeightSum_smooth P.centers P.radius_pos P.radius_lt P.locallyFinite)

end Yau.LeafProofs.L17Aux
