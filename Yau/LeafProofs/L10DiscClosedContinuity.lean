import Yau.LeafProofs.L10DiscContinuity

/-! Both the Green solution and its candidate first derivative are
continuous on the literal closed disc. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology ContDiff

namespace Yau.LeafProofs

theorem discGreen_norm_inverseNorm_bound {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) (hzw : z ≠ w) :
    ‖discGreenKernel z w‖ ≤ Real.pi⁻¹ * ‖z - w‖⁻¹ := by
  have hD : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hC : 0 < ‖1 - z * conj w‖ := norm_pos_iff.mpr (discGreen_denominator_ne_zero hz hw)
  have hDC := discGreen_denominator_ge hz hw.le
  have htwo : ‖1 - z * conj w‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z * conj w‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ * ‖w‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
      _ ≤ 2 := by nlinarith [norm_nonneg z, norm_nonneg w]
  have hlog : Real.log ‖1 - z * conj w‖ - Real.log ‖z - w‖ ≤ 2 / ‖z - w‖ := by
    rw [← Real.log_div hC.ne' hD.ne']
    exact ((Real.log_le_sub_one_of_pos (div_pos hC hD)).trans (by linarith)).trans
      (div_le_div_of_nonneg_right htwo hD.le)
  rw [discGreenKernel, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hD hDC))]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (2 / ‖z - w‖) := by
      exact mul_le_mul_of_nonneg_left (by linarith [hlog]) (by positivity)
    _ = _ := by field_simp

theorem discGreenSolution_integrand_near_mass {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
      ‖discGreenKernel z w • f w‖) ≤ 2 * M * r := by
  have hSol : IntegrableOn (fun w => ‖discGreenKernel z w • f w‖)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    ((discGreen_solution_integrable hf (by simpa using hz)).mono_set Set.inter_subset_left).norm
  have hInv : IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹)
      (Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r) volume :=
    (discGreen_inverseNorm_integrable_disc z).mono_set Set.inter_subset_left
  calc
    _ ≤ ∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r,
        (Real.pi⁻¹ * ‖z - w‖⁻¹) * M := by
      apply integral_mono_ae hSol ((hInv.const_mul _).mul_const _)
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball),
        ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
      rw [norm_smul]
      exact mul_le_mul (discGreen_norm_inverseNorm_bound hz (by simpa using hw.1) hne.symm)
        (hbound w (Metric.ball_subset_closedBall hw.1)) (norm_nonneg _) (by positivity)
    _ = (Real.pi⁻¹ * (∫ w in Metric.ball (0 : ℂ) 1 ∩ Metric.ball z r, ‖z - w‖⁻¹)) * M := by
      rw [integral_mul_const, integral_const_mul]
    _ ≤ (Real.pi⁻¹ * (2 * Real.pi * r)) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (discGreen_inverseNorm_near_mass z hr) (by positivity)) hM
    _ = _ := by field_simp

theorem discGreen_gradient_continuousAt_left {z w : ℂ} (hzw : z ≠ w)
    (hden : 1 - z * conj w ≠ 0) :
    ContinuousAt (fun y => fderiv ℝ (fun v => discGreenKernel v w) y) z := by
  have hN : ContDiffAt ℝ 2 (fun y : ℂ => y - w) z := by fun_prop
  have hC : ContDiffAt ℝ 2 (fun y : ℂ => 1 - y * conj w) z := by fun_prop
  have hG : ContDiffAt ℝ 2 (fun y => discGreenKernel y w) z := by
    apply ContDiffAt.mul contDiffAt_const
    exact ((hN.norm ℂ (sub_ne_zero.mpr hzw)).log
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzw))).sub
      ((hC.norm ℂ hden).log (norm_ne_zero_iff.mpr hden))
  exact hG.continuousAt_fderiv (by norm_num)

theorem discGreenDerivative_continuousOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discGreenDerivative f) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hMpos : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp))
  apply disc_integral_continuousOn_of_near_mass (K := discGreenDerivativeIntegrand f)
    (A := 2 * M) (B := Real.pi⁻¹ * M) (by positivity) (by positivity)
  · intro z hz
    exact discGreenDerivativeIntegrand_integrable hf (by simpa using hz)
  · intro z hz w hw hzw
    have hD := discGreen_gradient_continuousAt_left hzw
      (discGreen_denominator_ne_zero (by simpa using hz) (by simpa using hw))
    exact (((ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous.continuousAt.comp hD).clm_apply
      continuousAt_const).continuousWithinAt
  · intro z hz w hw hzw
    rw [discGreenDerivativeIntegrand, ContinuousLinearMap.norm_smulRight_apply]
    calc
      _ ≤ (Real.pi⁻¹ * ‖z - w‖⁻¹) * M := mul_le_mul
        (discGreen_gradient_bound (by simpa using hz) (by simpa using hw) hzw)
        (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro z hz r hr
    exact discGreenDerivativeIntegrand_near_mass hf hMpos hM (by simpa using hz) hr

theorem discGreenSolution_continuousOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discGreenSolution f) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hMpos : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp))
  apply disc_integral_continuousOn_of_near_mass (K := fun z w => discGreenKernel z w • f w)
    (A := 2 * M) (B := Real.pi⁻¹ * M) (by positivity) (by positivity)
  · exact fun z hz => discGreen_solution_integrable hf hz
  · intro z hz w hw hzw
    exact ((discGreen_differentiableAt (by simpa using hz) (by simpa using hw) hzw).continuousAt.smul
      continuousAt_const).continuousWithinAt
  · intro z hz w hw hzw
    rw [norm_smul]
    calc
      _ ≤ (Real.pi⁻¹ * ‖z - w‖⁻¹) * M := mul_le_mul
        (discGreen_norm_inverseNorm_bound (by simpa using hz) (by simpa using hw) hzw)
        (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro z hz r hr
    exact discGreenSolution_integrand_near_mass hf hMpos hM (by simpa using hz) hr

end Yau.LeafProofs
