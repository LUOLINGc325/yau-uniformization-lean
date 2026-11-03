import Yau.LeafProofs.L10GreenDifferential

/-! Absolute integrability and the literal zero boundary values of the Green integral. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Yau.LeafProofs

theorem discGreen_norm_bound {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) (hzw : z ≠ w) :
    ‖discGreenKernel z w‖ ≤
      (2 * Real.pi)⁻¹ * (Real.log 2 + |Real.log ‖z - w‖|) := by
  have hN : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hC : 0 < ‖1 - z * conj w‖ :=
    norm_pos_iff.mpr (discGreen_denominator_ne_zero hz hw)
  have htwo : ‖1 - z * conj w‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖z * conj w‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ * ‖w‖ := by rw [norm_one, norm_mul, Complex.norm_conj]
      _ ≤ 2 := by nlinarith [norm_nonneg z, norm_nonneg w]
  have hlo := Real.log_le_log hN (discGreen_denominator_ge hz hw.le)
  have hhi := Real.log_le_log hC htwo
  rw [discGreenKernel, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hlo)]
  gcongr
  linarith [neg_le_abs (Real.log ‖z - w‖)]

theorem discGreen_kernel_measurable (z : ℂ) : Measurable (discGreenKernel z) := by
  unfold discGreenKernel
  fun_prop

theorem discGreen_integrable {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    IntegrableOn (discGreenKernel z) (Metric.ball (0 : ℂ) 1) volume := by
  have hlog := L08_integrableOn_log_norm_sub_disc z 0 1
  have hfinite : volume (Metric.ball (0 : ℂ) 1) ≠ ⊤ :=
    (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) 1)).measure_lt_top.ne
  have hb := ((integrableOn_const hfinite : IntegrableOn
      (fun _ : ℂ => Real.log 2) (Metric.ball 0 1) volume).add hlog.norm).const_mul
        ((2 * Real.pi)⁻¹)
  apply hb.mono' (discGreen_kernel_measurable z).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
  exact discGreen_norm_bound (by simpa using hz) (by simpa using hw)
    hne.symm

def discGreenSolution (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in Metric.ball (0 : ℂ) 1, discGreenKernel z w • f w

theorem discGreen_solution_integrable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    IntegrableOn (fun w => discGreenKernel z w • f w) (Metric.ball (0 : ℂ) 1) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  apply (discGreen_integrable hz).smul_bdd M
  · exact (hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    exact hM w (Metric.ball_subset_closedBall hw)

theorem discGreenSolution_boundary (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) 1) : discGreenSolution f z = 0 := by
  unfold discGreenSolution
  have hn : ‖z‖ = 1 := by simpa using hz
  simp only [discGreen_boundary hn, zero_smul, integral_zero]

end Yau.LeafProofs
