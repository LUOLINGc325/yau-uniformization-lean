import Yau.Proofs.P08HeatMeasureBallLower

/-! Continuous data need no global L² hypothesis in the ball-to-heat
pairing: first multiply by a genuine compact cutoff that is one on the ball. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.P08Aux
open Yau Yau.LeafProofs L12Aux L18Aux L19Aux HeatMeasure
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem continuous_ball_integral_abs_le_heat (hn : 0 < n) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier)
    {L : ℝ} (hL : 0 < L) {w : M.Carrier → ℝ} (hw : Continuous w)
    (hi : Integrable (fun x => |w x|)
      (heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity))) :
    (∫ x in distBall g.form o L, |w x| ∂μ) ≤
      ballHeatConstant n * (μ (distBall g.form o L)).toReal *
        (∫ x, |w x| ∂heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)) := by
  let ν := heatEvalMeasure hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  obtain ⟨χ, hχ, hcχ, hχrange, hχone, _⟩ := exists_smooth_compact_cutoff g o hL
    (show L < L + 1 by linarith)
  let F : M.Carrier → ℝ := fun x => χ x * |w x|
  have hFcont : Continuous F := (continuous_of_smoothFn hχ).mul hw.abs
  have hFmem : MemLp F 2 μ := hFcont.memLp_of_hasCompactSupport hcχ.mul_right
  let f : Lp ℝ 2 μ := hFmem.toLp F
  have hf : (fun x => f x) =ᵐ[μ] F := hFmem.coeFn_toLp
  have hf0 : ∀ᵐ x ∂μ, 0 ≤ f x := by
    filter_upwards [hf] with x hx
    rw [hx]
    exact mul_nonneg (hχrange x).1 (abs_nonneg _)
  have hh := heatEvalMeasure_ball_lower hn g hcomplete hK hRic μ hμ o L hL f hf0
  have hball : (∫ x in distBall g.form o L, f x ∂μ) =
      ∫ x in distBall g.form o L, |w x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hf, ae_restrict_mem (measurableSet_distBall g o L)] with x hx hxb
    rw [hx]
    change χ x * |w x| = |w x|
    rw [hχone x ((mem_distBall_iff g o x hL).mp hxb).le, one_mul]
  have hνf : (fun x => f x) =ᵐ[ν] F :=
    (heatEvalMeasure_absolutelyContinuous hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity)).ae_eq hf
  have hcut : (∫ x, f x ∂ν) ≤ ∫ x, |w x| ∂ν := by
    apply integral_mono_ae (heatEvalMeasure_integrable hn g hcomplete hK hRic μ hμ o (2 * L ^ 2) (by positivity) f) hi
    filter_upwards [hνf] with x hx
    rw [hx]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχrange x).2
  rw [hball] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hcut
    (mul_nonneg (ballHeatConstant_pos n).le ENNReal.toReal_nonneg))

end Yau.NodeProofs.P08Aux
