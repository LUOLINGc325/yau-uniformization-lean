import Yau.Proofs.C04NormalModelJetsForms

/-! The same rescaled inverse parameter and its actual pulled-back Gram form. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pullbackModelLinear (d : ℝ) (L : E →L[ℝ] E) : E →L[ℝ] E := d⁻¹ • L

def pullbackModelParameter (d : ℝ) (ψ : E → E) (L : E →L[ℝ] E) (z : E) : E :=
  d • ψ (d⁻¹ • L z)

def pullbackModelMetric (d : ℝ) (A : E → E →L[ℝ] E) (ψ : E → E) (L : E →L[ℝ] E)
    (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  normalModelMetric ((A (pullbackModelParameter d ψ L z)).comp
    (fderiv ℝ (pullbackModelParameter d ψ L) z))

theorem pullbackModelMetric_eq_coframe (d : ℝ) (A : E → E →L[ℝ] E)
    (ψ : E → E) (L : E →L[ℝ] E) (z : E) :
    pullbackModelMetric d A ψ L z = normalModelMetric
      ((A (pullbackModelParameter d ψ L z)).comp (fderiv ℝ (pullbackModelParameter d ψ L) z)) := rfl

theorem pullbackModelMetric_eq_bilinearComp (d : ℝ) (A : E → E →L[ℝ] E)
    (ψ : E → E) (L : E →L[ℝ] E) (z : E) :
    pullbackModelMetric d A ψ L z =
      (normalModelMetric (A (pullbackModelParameter d ψ L z))).bilinearComp
        (fderiv ℝ (pullbackModelParameter d ψ L) z) (fderiv ℝ (pullbackModelParameter d ψ L) z) := by
  ext v w
  simp only [pullbackModelMetric, ContinuousLinearMap.bilinearComp_apply,
    normalModelMetric_apply, ContinuousLinearMap.comp_apply]

theorem pullback_model_linear_norm (d : ℝ) (hd : 0 < d)
    (L : E →L[ℝ] E) (hL : ‖L‖ ≤ (5 / 4 : ℝ)) :
    ‖pullbackModelLinear d L‖ ≤ 5 / (4 * d) := by
  calc
    ‖pullbackModelLinear d L‖ = d⁻¹ * ‖L‖ := by
      simp only [pullbackModelLinear, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
    _ ≤ d⁻¹ * (5 / 4) := mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hd.le)
    _ = 5 / (4 * d) := by field_simp

theorem pullback_model_linear_mem_ball (d : ℝ) (hd : 0 < d)
    (L : E →L[ℝ] E) (hL : ‖L‖ ≤ (5 / 4 : ℝ))
    {z : E} (hz : z ∈ Metric.ball (0 : E) (d / 16)) :
    pullbackModelLinear d L z ∈ Metric.ball (0 : E) (1 / 8 : ℝ) := by
  have hz' : ‖z‖ < d / 16 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hK : 0 < 5 / (4 * d) := by positivity
  rw [Metric.mem_ball, dist_zero_right]
  calc
    ‖pullbackModelLinear d L z‖ ≤ ‖pullbackModelLinear d L‖ * ‖z‖ :=
      (pullbackModelLinear d L).le_opNorm _
    _ ≤ 5 / (4 * d) * ‖z‖ :=
      mul_le_mul_of_nonneg_right (pullback_model_linear_norm d hd L hL) (norm_nonneg _)
    _ < 5 / (4 * d) * (d / 16) := mul_lt_mul_of_pos_left hz' hK
    _ = 5 / 64 := by field_simp; ring
    _ < 1 / 8 := by norm_num

theorem pullback_model_parameter_mem_ball (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hdR : d ≤ R / 4) (ψ : E → E) (L : E →L[ℝ] E) (hL : ‖L‖ ≤ (5 / 4 : ℝ))
    (hψnorm : ∀ w ∈ Metric.ball (0 : E) (1 / 8 : ℝ), ‖ψ w‖ ≤ (4 / 3 : ℝ) * ‖w‖)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (d / 16)) :
    pullbackModelParameter d ψ L z ∈ Metric.ball (0 : E) R := by
  have hw := pullback_model_linear_mem_ball d hd L hL hz
  have hz' : ‖z‖ < d / 16 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hb : ‖pullbackModelParameter d ψ L z‖ ≤ (5 / 3 : ℝ) * ‖z‖ := by
    calc
      ‖pullbackModelParameter d ψ L z‖ = d * ‖ψ (pullbackModelLinear d L z)‖ := by
        simp only [pullbackModelParameter, pullbackModelLinear, norm_smul, Real.norm_eq_abs,
          abs_of_pos hd, smul_apply]
      _ ≤ d * ((4 / 3 : ℝ) * (‖pullbackModelLinear d L‖ * ‖z‖)) :=
        mul_le_mul_of_nonneg_left
          ((hψnorm _ hw).trans (mul_le_mul_of_nonneg_left
            ((pullbackModelLinear d L).le_opNorm _) (by norm_num))) hd.le
      _ ≤ d * ((4 / 3 : ℝ) * (5 / (4 * d) * ‖z‖)) := by
        gcongr
        exact pullback_model_linear_norm d hd L hL
      _ = (5 / 3 : ℝ) * ‖z‖ := by field_simp
  rw [Metric.mem_ball, dist_zero_right]
  linarith

theorem pullback_model_parameter_smooth (d : ℝ) (hd : 0 < d)
    (ψ : E → E) (L : E →L[ℝ] E) (hL : ‖L‖ ≤ (5 / 4 : ℝ))
    (hψ : ContDiffOn ℝ ∞ ψ (Metric.ball (0 : E) (1 / 8 : ℝ))) :
    ContDiffOn ℝ ∞ (pullbackModelParameter d ψ L) (Metric.ball (0 : E) (d / 16)) := by
  exact contDiffOn_const.smul (hψ.comp (pullbackModelLinear d L).contDiff.contDiffOn
    (fun z hz => pullback_model_linear_mem_ball d hd L hL hz))

end Yau.Proofs.C04Aux
