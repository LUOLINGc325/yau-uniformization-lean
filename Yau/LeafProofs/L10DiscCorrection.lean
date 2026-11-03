import Yau.LeafProofs.L10DiscNewton

/-! The correction term is harmonic in the open disc. Its holomorphic
parameter integral uses a fixed positive denominator bound on each smaller disc. -/

noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology ContDiff Laplacian

namespace Yau.LeafProofs

private theorem discCorrection_slit {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - z * conj w ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hprod : ‖z * conj w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg z)).trans_lt (by simpa using hz)
  have hre := (le_abs_self (z * conj w).re).trans (Complex.abs_re_le_norm _)
  simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr (hre.trans_lt hprod)

private theorem discCorrection_ne_zero {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - z * conj w ≠ 0 := Complex.slitPlane_ne_zero (discCorrection_slit hz hw)

/-- The holomorphic integral from which the real logarithmic correction
is recovered by conjugation. -/
def discCorrectionHolomorphic (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in Metric.ball (0 : ℂ) 1, Complex.log (1 - z * conj w) * f w

private theorem discCorrection_integrand_continuousOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousOn (fun w => Complex.log (1 - z * conj w) * f w)
      (Metric.closedBall (0 : ℂ) 1) := by
  have hc : ContinuousOn (fun w : ℂ => 1 - z * conj w)
      (Metric.closedBall (0 : ℂ) 1) := by fun_prop
  exact (hc.clog (fun w hw => discCorrection_slit hz (by simpa using hw))).mul hf

private theorem discCorrection_derivative_continuousOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousOn (fun w => ((1 - z * conj w)⁻¹ * -conj w) * f w)
      (Metric.closedBall (0 : ℂ) 1) := by
  have hc : ContinuousOn (fun w : ℂ => 1 - z * conj w)
      (Metric.closedBall (0 : ℂ) 1) := by fun_prop
  exact ((hc.inv₀ (fun w hw => discCorrection_ne_zero hz (by simpa using hw))).mul
    (show ContinuousOn (fun w : ℂ => -conj w) _ by fun_prop)).mul hf

theorem discCorrectionHolomorphic_differentiableOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) :
    DifferentiableOn ℂ (discCorrectionHolomorphic f) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hzN : ‖z‖ < 1 := by simpa using hz
  let R : ℝ := (‖z‖ + 1) / 2
  have hzR : ‖z‖ < R := by dsimp [R]; linarith
  have hR : R < 1 := by dsimp [R]; linarith
  have hs : Metric.ball (0 : ℂ) R ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds (by simpa using hzR)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  have hMpos : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0 (by simp))
  have hI : IntegrableOn (fun w => Complex.log (1 - z * conj w) * f w)
      (Metric.ball (0 : ℂ) 1) volume :=
    ((discCorrection_integrand_continuousOn hf hzN).integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun w => Complex.log (1 - x * conj w) * f w)
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    filter_upwards [hs] with x hx
    exact ((discCorrection_integrand_continuousOn hf
      ((show ‖x‖ < R by simpa using hx).trans hR)).mono
        Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hDmeas : AEStronglyMeasurable
      (fun w => ((1 - z * conj w)⁻¹ * -conj w) * f w)
      (volume.restrict (Metric.ball (0 : ℂ) 1)) :=
    ((discCorrection_derivative_continuousOn hf hzN).mono
      Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hDbound : ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : ℂ) 1)),
      ∀ x ∈ Metric.ball (0 : ℂ) R,
        ‖((1 - x * conj w)⁻¹ * -conj w) * f w‖ ≤ (1 - R)⁻¹ * M := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    intro x hx
    have hwN : ‖w‖ ≤ 1 := (show ‖w‖ < 1 by simpa using hw).le
    have hxN : ‖x‖ < R := by simpa using hx
    have hlower : 1 - R ≤ ‖1 - x * conj w‖ := by
      have hp : ‖x * conj w‖ ≤ R := by
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul_of_nonneg_left hwN (norm_nonneg x)).trans (by simpa using hxN.le)
      have ht := norm_sub_le (1 - x * conj w) (-x * conj w)
      have hh : 1 - x * conj w - (-x * conj w) = (1 : ℂ) := by ring
      rw [hh, norm_one, neg_mul, norm_neg] at ht
      linarith
    rw [norm_mul, norm_mul, norm_inv, norm_neg, Complex.norm_conj]
    have hInv : ‖1 - x * conj w‖⁻¹ ≤ (1 - R)⁻¹ :=
      (inv_le_inv₀ ((by linarith : 0 < 1 - R).trans_le hlower)
        (by linarith : 0 < 1 - R)).2 hlower
    calc
      _ ≤ (1 - R)⁻¹ * 1 * M :=
        mul_le_mul (mul_le_mul hInv hwN (norm_nonneg w) (by positivity))
          (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hDiff : ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : ℂ) 1)),
      ∀ x ∈ Metric.ball (0 : ℂ) R,
        HasDerivAt (fun x => Complex.log (1 - x * conj w) * f w)
          (((1 - x * conj w)⁻¹ * -conj w) * f w) x := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    intro x hx
    simpa only [Function.comp_def, id_eq, one_mul] using
      ((Complex.hasDerivAt_log (discCorrection_slit
      ((show ‖x‖ < R by simpa using hx).trans hR)
      (show ‖w‖ ≤ 1 by simpa using (Metric.ball_subset_closedBall hw)))).comp x
      (((hasDerivAt_id x).mul_const (conj w)).const_sub 1)).mul_const (f w)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hFmeas hI hDmeas
    hDbound (integrableOn_const (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
      |>.mono_set Metric.ball_subset_closedBall) hDiff).2.differentiableAt.differentiableWithinAt

/-- The actual real-logarithm correction in the Green kernel. -/
def discGreenCorrection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in Metric.ball (0 : ℂ) 1, Real.log ‖1 - z * conj w‖ • f w

private theorem discGreenCorrection_eq {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) {z : ℂ} (hz : ‖z‖ < 1) :
    discGreenCorrection f z = (1 / 2 : ℂ) •
      (discCorrectionHolomorphic f z + conj (discCorrectionHolomorphic (fun w => conj (f w)) z)) := by
  have hfc : ContinuousOn (fun w => conj (f w)) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.conjCLE.continuous.comp_continuousOn hf
  have hIf : IntegrableOn (fun w => Complex.log (1 - z * conj w) * f w)
      (Metric.ball (0 : ℂ) 1) volume :=
    ((discCorrection_integrand_continuousOn hf hz).integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hIc : IntegrableOn (fun w => Complex.log (1 - z * conj w) * conj (f w))
      (Metric.ball (0 : ℂ) 1) volume :=
    ((discCorrection_integrand_continuousOn hfc hz).integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hconj : conj (∫ w in Metric.ball (0 : ℂ) 1,
      Complex.log (1 - z * conj w) * conj (f w)) =
      ∫ w in Metric.ball (0 : ℂ) 1, conj (Complex.log (1 - z * conj w) * conj (f w)) :=
    (Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hIc).symm
  have hIconj : IntegrableOn (fun w => conj (Complex.log (1 - z * conj w) * conj (f w)))
      (Metric.ball (0 : ℂ) 1) volume := Complex.conjCLE.toContinuousLinearMap.integrable_comp hIc
  rw [discGreenCorrection, discCorrectionHolomorphic, discCorrectionHolomorphic,
    hconj, ← integral_add hIf hIconj, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  apply Complex.ext <;> simp [Complex.log_re, Complex.mul_re, Complex.mul_im] <;> ring

theorem discGreenCorrection_contDiffOn {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (discGreenCorrection f) (Metric.ball (0 : ℂ) 1) := by
  have hfc : ContinuousOn (fun w => conj (f w)) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.conjCLE.continuous.comp_continuousOn hf
  have hH := ((discCorrectionHolomorphic_differentiableOn hf).contDiffOn
    Metric.isOpen_ball : ContDiffOn ℂ ∞ _ _).restrict_scalars ℝ
  have hC := ((discCorrectionHolomorphic_differentiableOn hfc).contDiffOn
    Metric.isOpen_ball : ContDiffOn ℂ ∞ _ _).restrict_scalars ℝ
  have h := (hH.add (Complex.conjCLE.contDiff.comp_contDiffOn hC)).const_smul (1 / 2 : ℂ)
  exact h.congr (fun z hz => discGreenCorrection_eq hf (by simpa using hz))

theorem discGreenCorrection_laplacian {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    LeafCandidates.planarLaplacian (discGreenCorrection f) z = 0 := by
  have hfc : ContinuousOn (fun w => conj (f w)) (Metric.closedBall (0 : ℂ) 1) :=
    Complex.conjCLE.continuous.comp_continuousOn hf
  have hH := ((discCorrectionHolomorphic_differentiableOn hf).analyticOnNhd Metric.isOpen_ball z hz).harmonicAt
  have hC : InnerProductSpace.HarmonicAt
      (fun y => conj (discCorrectionHolomorphic (fun w => conj (f w)) y)) z :=
    (((discCorrectionHolomorphic_differentiableOn hfc).analyticOnNhd
      Metric.isOpen_ball z hz).harmonicAt).comp_CLM Complex.conjCLE.toContinuousLinearMap
  have hSum : ContDiffAt ℝ 2 (discCorrectionHolomorphic f +
      fun y => conj (discCorrectionHolomorphic (fun w => conj (f w)) y)) z := hH.1.add hC.1
  have heq : discGreenCorrection f =ᶠ[𝓝 z] (1 / 2 : ℂ) •
      (discCorrectionHolomorphic f + fun y => conj (discCorrectionHolomorphic (fun w => conj (f w)) y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact discGreenCorrection_eq hf (by simpa using hy)
  rw [disc_planarLaplacian_eq_laplacian
    (((discGreenCorrection_contDiffOn hf).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).of_le (by simp)),
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
    InnerProductSpace.laplacian_smul (1 / 2 : ℂ) hSum, hH.1.laplacian_add hC.1]
  simp [hH.2.eq_of_nhds, hC.2.eq_of_nhds]

end Yau.LeafProofs
