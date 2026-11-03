import Yau.Proofs.C04BoundedGeometryChartsUniformInverse

/-! The fixed inverse parameter normalizes the center differential exactly. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

def normalizedInverseParameter (e : OpenPartialHomeomorph E E) (L : E →L[ℝ] E)
    (d : ℝ) (z : E) : E := d • e.symm (d⁻¹ • L z)

@[simp] theorem normalizedInverseParameter_zero (e : OpenPartialHomeomorph E E)
    (L : E →L[ℝ] E) (d : ℝ) (he0 : e.symm 0 = 0) : normalizedInverseParameter e L d 0 = 0 := by
  simp only [normalizedInverseParameter, map_zero, smul_zero, he0]

theorem normalizedInverseParameter_argument_mem (L : E →L[ℝ] E)
    (hL : ‖L‖ ≤ (5 / 4 : ℝ)) {d : ℝ} (hd : 0 < d)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (d / 16)) :
    d⁻¹ • L z ∈ Metric.ball (0 : E) (1 / 8 : ℝ) := by
  have hn : ‖z‖ < d / 16 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hLz := (L.le_opNorm z).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg z))
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  apply (mul_lt_mul_iff_right₀ hd).mp
  rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  nlinarith

theorem normalizedInverseParameter_norm_le (e : OpenPartialHomeomorph E E) (L : E →L[ℝ] E)
    (hL : ‖L‖ ≤ (5 / 4 : ℝ)) {d : ℝ} (hd : 0 < d)
    (ht : Metric.ball (0 : E) (1 / 8 : ℝ) ⊆ e.target)
    (he : ∀ w ∈ e.target, ‖e.symm w‖ ≤ (4 / 3 : ℝ) * ‖w‖)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (d / 16)) :
    ‖normalizedInverseParameter e L d z‖ ≤ (5 / 3 : ℝ) * ‖z‖ := by
  have hw := normalizedInverseParameter_argument_mem L hL hd hz
  have H := he _ (ht hw)
  rw [normalizedInverseParameter, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  calc
    _ ≤ d * ((4 / 3 : ℝ) * ‖d⁻¹ • L z‖) := mul_le_mul_of_nonneg_left H hd.le
    _ = (4 / 3 : ℝ) * ‖L z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
      field_simp
    _ ≤ (4 / 3 : ℝ) * ((5 / 4 : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((L.le_opNorm z).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg z))) (by norm_num)
    _ = _ := by ring

variable [CompleteSpace E]

theorem normalizedInverseParameter_smoothOn (e : OpenPartialHomeomorph E E) (L : E →L[ℝ] E)
    (hL : ‖L‖ ≤ (5 / 4 : ℝ)) {d : ℝ} (hd : 0 < d)
    (ht : Metric.ball (0 : E) (1 / 8 : ℝ) ⊆ e.target)
    (he : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (normalizedInverseParameter e L d) (Metric.ball (0 : E) (d / 16)) := by
  have harg : ContDiff ℝ ∞ (fun z => d⁻¹ • L z) := L.contDiff.const_smul d⁻¹
  exact (he.comp harg.contDiffOn (fun z hz => ht (normalizedInverseParameter_argument_mem L hL hd hz))).const_smul d

theorem normalizedInverseParameter_hasFDerivAt_zero (e : OpenPartialHomeomorph E E)
    (F : E → E) (he : (e : E → E) = F) (hF : ContDiff ℝ ∞ F)
    (h0 : e.symm 0 = 0) (ht : (0 : E) ∈ e.target)
    (hi : (fderiv ℝ F 0).IsInvertible) {d : ℝ} (hd : d ≠ 0) :
    HasFDerivAt (normalizedInverseParameter e (fderiv ℝ F 0) d) (ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨D, hD⟩ := hi
  have hDF : HasFDerivAt e (D : E →L[ℝ] E) (e.symm 0) := by
    rw [h0, he, hD]
    exact (hF.differentiable (by simp) 0).hasFDerivAt
  have hψ := e.hasFDerivAt_symm ht hDF
  let T : E →L[ℝ] E := d⁻¹ • fderiv ℝ F 0
  have hT : HasFDerivAt (fun z => d⁻¹ • fderiv ℝ F 0 z) T 0 := T.hasFDerivAt
  have hψ' : HasFDerivAt e.symm (D.symm : E →L[ℝ] E) (T 0) := by
    simpa only [map_zero] using hψ
  have H := (hψ'.comp 0 hT).const_smul d
  have hder : d • ((D.symm : E →L[ℝ] E).comp T) = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    change d • D.symm (d⁻¹ • fderiv ℝ F 0 v) = v
    rw [← hD]
    simp only [map_smul, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply,
      smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [hder] at H
  exact H

end Yau.Proofs.C04ChartsAux
