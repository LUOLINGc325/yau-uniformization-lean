import Yau.Proofs.V02HarmonicExtension

/-! Dirichlet energy is minimized by the actual smooth harmonic extension.
The integration by parts uses a zero-boundary difference, not holomorphicity
of the original function. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

theorem real_harmonic_energy_minimizes {u H : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hH : ContDiffOn ℝ ∞ H (Metric.closedBall (0 : ℂ) 1))
    (hB : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = H z)
    (hΔ : ∀ z ∈ Metric.ball (0 : ℂ) 1, discEnergyRealLaplacian H z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq H z) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z := by
  let v : ℂ → ℝ := fun z => u z - H z
  let p := discEnergyPartial H (1 : ℂ)
  let q := discEnergyPartial H Complex.I
  let C : ℂ → ℝ := fun z => discEnergyPartial v 1 z * p z +
    discEnergyPartial v Complex.I z * q z
  have hv : ContDiffOn ℝ ∞ v (Metric.closedBall (0 : ℂ) 1) := hu.sub hH
  have hp : ContDiffOn ℝ ∞ p (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hH 1
  have hq : ContDiffOn ℝ ∞ q (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hH Complex.I
  let F : ℂ → ℂ := fun z => ((v z * p z : ℝ) : ℂ) + ((v z * q z : ℝ) : ℂ) * Complex.I
  have hF : ContDiffOn ℝ ∞ F (Metric.closedBall (0 : ℂ) 1) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (hv.mul hp)).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hv.mul hq)).mul contDiffOn_const)
  have hdiv (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (fderiv ℝ F z 1).re + (fderiv ℝ F z Complex.I).im = C z := by
    have hdv := (discEnergy_contDiffAt hv hz).differentiableAt (by simp)
    have hdp := (discEnergy_contDiffAt hp hz).differentiableAt (by simp)
    have hdq := (discEnergy_contDiffAt hq hz).differentiableAt (by simp)
    unfold F
    rw [discEnergy_coord_fderiv (p := fun w => v w * p w) (q := fun w => v w * q w)
      (hdv.mul hdp) (hdv.mul hdq),
      discEnergy_coord_fderiv (p := fun w => v w * p w) (q := fun w => v w * q w)
      (hdv.mul hdp) (hdv.mul hdq)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
    rw [fderiv_fun_mul hdv hdp, fderiv_fun_mul hdv hdq]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← discEnergyPartial_eq_fderiv v 1 hz, ← discEnergyPartial_eq_fderiv v Complex.I hz,
      ← discEnergyPartial_eq_fderiv p 1 hz, ← discEnergyPartial_eq_fderiv q Complex.I hz]
    calc
      _ = C z + v z * discEnergyRealLaplacian H z := by
        unfold C p q discEnergyRealLaplacian
        ring
      _ = _ := by rw [hΔ z hz]; ring
  have hboundary : (∫ θ in (-Real.pi)..Real.pi,
      inner ℝ (L08_unitCircle θ) (F (L08_unitCircle θ))) = 0 := by
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        have h0 : v (L08_unitCircle θ) = 0 :=
          sub_eq_zero.mpr (hB _ (by simp [L08_norm_unitCircle]))
        simp only [F, h0, zero_mul, Complex.ofReal_zero, add_zero, inner_zero_right]
      _ = 0 := by simp
  have hcross : (∫ z in Metric.ball (0 : ℂ) 1, C z) = 0 :=
    (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv).symm.trans
      ((discEnergy_integral_divergence_smooth hF).trans hboundary)
  have hpoint (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      discEnergyRealGradientSq H z ≤ discEnergyRealGradientSq u z - 2 * C z := by
    have hsub (a : ℂ) : discEnergyPartial v a z =
        discEnergyPartial u a z - discEnergyPartial H a z := by
      unfold v discEnergyPartial
      rw [fderivWithin_fun_sub (disc_closedBall_uniqueDiffOn z (Metric.ball_subset_closedBall hz))
        ((hu.differentiableOn (by simp)) z (Metric.ball_subset_closedBall hz))
        ((hH.differentiableOn (by simp)) z (Metric.ball_subset_closedBall hz))]
      rfl
    unfold discEnergyRealGradientSq C p q
    rw [hsub 1, hsub Complex.I]
    nlinarith [sq_nonneg (discEnergyPartial u 1 z - discEnergyPartial H 1 z),
      sq_nonneg (discEnergyPartial u Complex.I z - discEnergyPartial H Complex.I z)]
  have hIu := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hu)
  have hIH := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hH)
  have hIC : IntegrableOn C (Metric.ball (0 : ℂ) 1) := discEnergy_integrableOn
    (((discEnergyPartial_contDiffOn hv 1).continuousOn.mul hp.continuousOn).add
      ((discEnergyPartial_contDiffOn hv Complex.I).continuousOn.mul hq.continuousOn))
  have hle := integral_mono_ae hIH (hIu.sub (hIC.const_mul 2)) (by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hpoint z hz)
  simp only [Pi.sub_apply] at hle
  rw [integral_sub hIu (hIC.const_mul 2), integral_const_mul, hcross, mul_zero, sub_zero] at hle
  exact hle

end Yau.Blueprint.V02Proof
