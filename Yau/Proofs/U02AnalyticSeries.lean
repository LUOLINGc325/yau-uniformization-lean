import Yau.Proofs.U02AnalyticRadius
import Yau.Proofs.U02AnalyticAffine
import Mathlib.Analysis.Complex.TaylorSeries

open scoped ContDiff Topology
open Set Metric ENNReal NNReal

namespace U02AnalyticAux

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem hasFPowerSeriesOnBall_of_complex_contDiffOn_infty
    {f : E → F} {x : E} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : ContDiffOn ℂ ∞ f (ball x R))
    (hb : ∀ y ∈ ball x R, ‖f y‖ ≤ C) :
    HasFPowerSeriesOnBall f (complexTaylorSeries f x) x
      (ENNReal.ofReal (R / (2 * Real.exp 1))) := by
  refine { r_le := complexTaylorSeries_radius_bound hR hC hf hb
           r_pos := ENNReal.ofReal_pos.mpr (by positivity)
           hasSum := ?_ }
  intro v hv
  have hv' : ‖v‖ < R / (2 * Real.exp 1) := by
    rw [ENNReal.ofReal] at hv
    simpa [Metric.eball_coe, mem_ball, dist_eq_norm, Real.coe_toNNReal _ (by positivity : 0 ≤ R / (2 * Real.exp 1))] using hv
  have hrR : R / (2 * Real.exp 1) ≤ R / 2 := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    gcongr
    linarith
  have hm : MapsTo (fun z : ℂ ↦ x + z • v) (ball 0 2) (ball x R) := by
    intro z hz
    have hz' : ‖z‖ < 2 := by simpa [mem_ball, dist_eq_norm] using hz
    have hvR := hv'.trans_le hrR
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left, norm_smul] using
      calc
        ‖z‖ * ‖v‖ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hz'.le (norm_nonneg _)
        _ < R := by linarith
  have hl : ContDiff ℂ ∞ (fun z : ℂ ↦ x + z • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hg : DifferentiableOn ℂ (fun z : ℂ ↦ f (x + z • v)) (ball 0 2) :=
    (hf.differentiableOn (by simp)).comp (hl.differentiable (by simp)).differentiableOn hm
  have hsum := Complex.hasSum_taylorSeries_on_ball (c := 0) (r := 2) (z := 1) hg
    (by norm_num [mem_ball, dist_eq_norm])
  simpa only [sub_zero, one_pow, one_smul,
    iteratedDeriv_complex_line_zero isOpen_ball hf (mem_ball_self hR),
    complexTaylorSeries, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using hsum

theorem analyticOnNhd_of_complex_contDiffOn_infty
    {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℂ ∞ f s) : AnalyticOnNhd ℂ f s := by
  intro x hx
  have hU := hf.continuousOn.isOpen_inter_preimage hs (isOpen_ball (x := f x) (ε := 1))
  have hxU : x ∈ s ∩ f ⁻¹' ball (f x) 1 := ⟨hx, by simp⟩
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
  have hbound : ∀ y ∈ ball x R, ‖f y‖ ≤ ‖f x‖ + 1 := by
    intro y hy
    have hdist : ‖f y - f x‖ < 1 := by
      simpa [mem_ball, dist_eq_norm] using (hsub hy).2
    calc
      ‖f y‖ = ‖(f y - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖f y - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ ‖f x‖ + 1 := by linarith
  exact (hasFPowerSeriesOnBall_of_complex_contDiffOn_infty hR (by positivity)
    (hf.mono (fun y hy => (hsub hy).1)) hbound).analyticAt

end U02AnalyticAux
