import Yau.LeafProofs.L10GreenKernel

/-! Pointwise bounds for the actual derivatives of the disc Green kernel. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate ContDiff

namespace Yau.LeafProofs

theorem discGreen_logNorm_differentiableAt {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun z : ℂ => Real.log ‖z‖) z := by
  exact ((contDiffAt_norm (n := 1) ℂ hz).differentiableAt (by norm_num)).log
    (norm_ne_zero_iff.mpr hz)

theorem discGreen_norm_fderiv_logNorm {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (fun z : ℂ => Real.log ‖z‖) z‖ = ‖z‖⁻¹ := by
  have hd : DifferentiableAt ℝ (fun z : ℂ => ‖z‖) z :=
    (contDiffAt_norm (n := 1) ℂ hz).differentiableAt (by norm_num)
  rw [fderiv.log hd (norm_ne_zero_iff.mpr hz), norm_smul, norm_fderiv_norm hd,
    mul_one, norm_inv, Real.norm_of_nonneg (norm_nonneg _)]

theorem discGreen_norm_fderiv_logNorm_affine
    (L : ℂ →L[ℝ] ℂ) (c z : ℂ) (hz : c + L z ≠ 0) :
    ‖fderiv ℝ (fun y => Real.log ‖c + L y‖) z‖ ≤ ‖L‖ / ‖c + L z‖ := by
  have ha : HasFDerivAt (fun y => c + L y) L z := by
    simpa using L.hasFDerivAt.const_add c
  have hd : HasFDerivAt (fun y => Real.log ‖c + L y‖)
      ((fderiv ℝ (fun z : ℂ => Real.log ‖z‖) (c + L z)).comp L) z := by
    simpa only [Function.comp_def] using
      (discGreen_logNorm_differentiableAt hz).hasFDerivAt.comp z ha
  rw [hd.fderiv]
  calc
    _ ≤ ‖fderiv ℝ (fun z : ℂ => Real.log ‖z‖) (c + L z)‖ * ‖L‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by rw [discGreen_norm_fderiv_logNorm hz]; ring

def discGreenCorrectionLinear (w : ℂ) : ℂ →L[ℝ] ℂ :=
  -((ContinuousLinearMap.mul ℝ ℂ).flip (conj w))

theorem discGreenCorrectionLinear_apply (w z : ℂ) :
    discGreenCorrectionLinear w z = -(z * conj w) := rfl

theorem discGreenCorrectionLinear_norm_le (w : ℂ) :
    ‖discGreenCorrectionLinear w‖ ≤ ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w)
  intro z
  simp [discGreenCorrectionLinear_apply, mul_comm]

theorem discGreen_norm_fderiv_correction {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) :
    ‖fderiv ℝ (fun y => Real.log ‖1 - y * conj w‖) z‖ ≤
      ‖w‖ / ‖1 - z * conj w‖ := by
  have hne := discGreen_denominator_ne_zero hz hw
  have hbound := discGreen_norm_fderiv_logNorm_affine (discGreenCorrectionLinear w) 1 z
    (by simpa only [discGreenCorrectionLinear_apply, ← sub_eq_add_neg] using hne)
  simp only [discGreenCorrectionLinear_apply, ← sub_eq_add_neg] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right (discGreenCorrectionLinear_norm_le w)
    (norm_nonneg _))

theorem discGreen_norm_fderiv_newton {z w : ℂ} (hzw : z ≠ w) :
    ‖fderiv ℝ (fun y => Real.log ‖y - w‖) z‖ ≤ ‖z - w‖⁻¹ := by
  have hb := discGreen_norm_fderiv_logNorm_affine (ContinuousLinearMap.id ℝ ℂ) (-w) z
    (by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hzw)
  simpa [sub_eq_add_neg, add_comm, one_div] using hb

theorem discGreen_differentiableAt {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) (hzw : z ≠ w) :
    DifferentiableAt ℝ (fun y => discGreenKernel y w) z := by
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · exact (discGreen_logNorm_differentiableAt (sub_ne_zero.mpr hzw)).comp z
      (differentiableAt_id.sub_const w)
  · exact (discGreen_logNorm_differentiableAt (discGreen_denominator_ne_zero hz hw)).comp z
      (show DifferentiableAt ℝ (fun y : ℂ => 1 - y * conj w) z by fun_prop)

theorem discGreen_gradient_bound {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) (hzw : z ≠ w) :
    ‖fderiv ℝ (fun y => discGreenKernel y w) z‖ ≤
      (Real.pi)⁻¹ * ‖z - w‖⁻¹ := by
  have hN : DifferentiableAt ℝ (fun y => Real.log ‖y - w‖) z :=
    (discGreen_logNorm_differentiableAt (sub_ne_zero.mpr hzw)).comp z
      (differentiableAt_id.sub_const w)
  have hC : DifferentiableAt ℝ (fun y => Real.log ‖1 - y * conj w‖) z := by
    simpa only [Function.comp_def] using
      (discGreen_logNorm_differentiableAt (discGreen_denominator_ne_zero hz hw)).comp z
        (show DifferentiableAt ℝ (fun y : ℂ => 1 - y * conj w) z by fun_prop)
  have hD : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hcor : ‖w‖ / ‖1 - z * conj w‖ ≤ ‖z - w‖⁻¹ := by
    calc
      _ ≤ 1 / ‖1 - z * conj w‖ := div_le_div_of_nonneg_right hw.le (norm_nonneg _)
      _ ≤ 1 / ‖z - w‖ := one_div_le_one_div_of_le hD (discGreen_denominator_ge hz hw.le)
      _ = _ := one_div _
  change ‖fderiv ℝ (fun y => (2 * Real.pi)⁻¹ *
    (Real.log ‖y - w‖ - Real.log ‖1 - y * conj w‖)) z‖ ≤ _
  change ‖fderiv ℝ (fun y => (2 * Real.pi)⁻¹ *
    ((fun y => Real.log ‖y - w‖) - (fun y => Real.log ‖1 - y * conj w‖)) y) z‖ ≤ _
  rw [fderiv_const_mul (hN.sub hC), fderiv_sub hN hC, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (‖fderiv ℝ (fun y => Real.log ‖y - w‖) z‖ +
        ‖fderiv ℝ (fun y => Real.log ‖1 - y * conj w‖) z‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (2 * Real.pi)⁻¹ * (‖z - w‖⁻¹ + ‖z - w‖⁻¹) := by
      gcongr
      · exact discGreen_norm_fderiv_newton hzw
      · exact (discGreen_norm_fderiv_correction hz hw).trans hcor
    _ = _ := by field_simp; ring

end Yau.LeafProofs
