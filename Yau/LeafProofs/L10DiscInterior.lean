import Yau.LeafProofs.L10DiscCorrection

/-! The explicit Green integral is an actual interior solution of the
original complex-valued planar Poisson equation. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology ContDiff Laplacian

namespace Yau.LeafProofs

theorem discNewtonPotential_integrable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) (z : ℂ) :
    IntegrableOn (fun w => Real.log ‖z - w‖ • f w) (Metric.ball (0 : ℂ) 1) volume := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  exact (L08_integrableOn_log_norm_sub_disc z 0 1).smul_bdd M
    ((hf.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
        exact hM w (Metric.ball_subset_closedBall hw))

theorem discGreenCorrection_integrable {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    IntegrableOn (fun w => Real.log ‖1 - z * conj w‖ • f w)
      (Metric.ball (0 : ℂ) 1) volume := by
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, 1 - z * conj w ≠ 0 := by
    intro w hw
    have hp : ‖z * conj w‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul_of_nonneg_left (show ‖w‖ ≤ 1 by simpa using hw)
        (norm_nonneg z)).trans_lt (by simpa using hz)
    intro h
    have hh : z * conj w = 1 := by linear_combination -h
    simp [hh] at hp
  have hc : ContinuousOn (fun w : ℂ => 1 - z * conj w)
      (Metric.closedBall (0 : ℂ) 1) := by fun_prop
  exact (((hc.norm.log (fun w hw => norm_ne_zero_iff.mpr (hne w hw))).smul hf).integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall

theorem discGreenSolution_eq_newton_sub_correction {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    discGreenSolution f z = (2 * Real.pi)⁻¹ •
      (discNewtonPotential f z - discGreenCorrection f z) := by
  rw [discGreenSolution, discNewtonPotential, discGreenCorrection,
    ← integral_sub (discNewtonPotential_integrable hf z) (discGreenCorrection_integrable hf hz),
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  simp [discGreenKernel, mul_smul, sub_smul]

theorem discGreenSolution_contDiffOn_interior {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discGreenSolution f) (Metric.ball (0 : ℂ) 1) := by
  have h := ((discNewtonPotential_contDiffOn hf).sub
    (discGreenCorrection_contDiffOn hf.continuousOn)).const_smul ((2 * Real.pi)⁻¹)
  exact h.congr (fun z hz => discGreenSolution_eq_newton_sub_correction hf.continuousOn (by simpa using hz))

theorem discGreenSolution_laplacian {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    LeafCandidates.planarLaplacian (discGreenSolution f) z = f z := by
  have hN : ContDiffAt ℝ 2 (discNewtonPotential f) z :=
    ((discNewtonPotential_contDiffOn hf).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  have hC : ContDiffAt ℝ 2 (discGreenCorrection f) z :=
    ((discGreenCorrection_contDiffOn hf.continuousOn).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)
  have heq : discGreenSolution f =ᶠ[𝓝 z] (2 * Real.pi)⁻¹ •
      (discNewtonPotential f - discGreenCorrection f) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact discGreenSolution_eq_newton_sub_correction hf.continuousOn (by simpa using hy)
  have hSub : ContDiffAt ℝ 2 (discNewtonPotential f - discGreenCorrection f) z := hN.sub hC
  rw [disc_planarLaplacian_eq_laplacian
    (((discGreenSolution_contDiffOn_interior hf).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)),
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
    InnerProductSpace.laplacian_smul ((2 * Real.pi)⁻¹) hSub,
    hN.laplacian_sub hC, ← disc_planarLaplacian_eq_laplacian hN,
    ← disc_planarLaplacian_eq_laplacian hC, discNewtonPotential_laplacian hf hz,
    discGreenCorrection_laplacian hf.continuousOn hz, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_smul]

end Yau.LeafProofs
