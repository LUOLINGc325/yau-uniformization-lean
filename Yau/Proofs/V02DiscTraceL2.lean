import Yau.Proofs.V02DiscDbarEnergy

/-! The L² part of the nonholomorphic trace estimate. A radial divergence
multiplier controls the full boundary trace, including its constant mode. -/

open scoped Topology ContDiff
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.LeafProofs

theorem real_disc_trace_L2_bound {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    (∫ θ in (-Real.pi)..Real.pi, u (L08_unitCircle θ) ^ 2) ≤
      3 * (∫ z in Metric.ball (0 : ℂ) 1, u z ^ 2) +
        ∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z := by
  let p : ℂ → ℝ := fun z => u z ^ 2 * z.re
  let q : ℂ → ℝ := fun z => u z ^ 2 * z.im
  let D : ℂ → ℝ := fun z => 2 * (u z ^ 2 + u z *
    (z.re * discEnergyPartial u 1 z + z.im * discEnergyPartial u Complex.I z))
  have hp : ContDiffOn ℝ ∞ p (Metric.closedBall (0 : ℂ) 1) :=
    (hu.pow 2).mul Complex.reCLM.contDiff.contDiffOn
  have hq : ContDiffOn ℝ ∞ q (Metric.closedBall (0 : ℂ) 1) :=
    (hu.pow 2).mul Complex.imCLM.contDiff.contDiffOn
  have hF : ContDiffOn ℝ ∞ (fun z => (p z : ℂ) + (q z : ℂ) * Complex.I)
      (Metric.closedBall (0 : ℂ) 1) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hp).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn hq).mul contDiffOn_const)
  have hdiv (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (fderiv ℝ (fun w => (p w : ℂ) + (q w : ℂ) * Complex.I) z 1).re +
        (fderiv ℝ (fun w => (p w : ℂ) + (q w : ℂ) * Complex.I) z Complex.I).im = D z := by
    have hdu := (discEnergy_contDiffAt hu hz).differentiableAt (by simp)
    rw [discEnergy_coord_fderiv ((discEnergy_contDiffAt hp hz).differentiableAt (by simp))
      ((discEnergy_contDiffAt hq hz).differentiableAt (by simp)),
      discEnergy_coord_fderiv ((discEnergy_contDiffAt hp hz).differentiableAt (by simp))
      ((discEnergy_contDiffAt hq hz).differentiableAt (by simp))]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add, p, q]
    have hpow : DifferentiableAt ℝ (fun w => u w ^ 2) z := hdu.pow 2
    have hre : DifferentiableAt ℝ (fun w : ℂ => w.re) z := Complex.reCLM.differentiableAt
    have him : DifferentiableAt ℝ (fun w : ℂ => w.im) z := Complex.imCLM.differentiableAt
    rw [fderiv_fun_mul hpow hre, fderiv_fun_mul hpow him]
    have hp2 : fderiv ℝ (fun w => u w ^ 2) z = ((2 : ℝ) * u z ^ (2 - 1)) • fderiv ℝ u z :=
      by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using fderiv_fun_pow 2 hdu
    have hrD : fderiv ℝ (fun w : ℂ => w.re) z = Complex.reCLM := Complex.reCLM.fderiv
    have hiD : fderiv ℝ (fun w : ℂ => w.im) z = Complex.imCLM := Complex.imCLM.fderiv
    rw [hp2, hrD, hiD]
    simp only [add_apply, smul_apply, smul_eq_mul, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.one_re, Complex.I_im]
    unfold D
    rw [discEnergyPartial_eq_fderiv u 1 hz, discEnergyPartial_eq_fderiv u Complex.I hz]
    ring
  have hboundary (θ : ℝ) :
      inner ℝ (L08_unitCircle θ) ((p (L08_unitCircle θ) : ℂ) +
        (q (L08_unitCircle θ) : ℂ) * Complex.I) = u (L08_unitCircle θ) ^ 2 := by
    have heq : (p (L08_unitCircle θ) : ℂ) + (q (L08_unitCircle θ) : ℂ) * Complex.I =
        u (L08_unitCircle θ) ^ 2 • L08_unitCircle θ := by
      simp only [p, q, Complex.real_smul, Complex.ofReal_mul]
      rw [mul_assoc, ← mul_add, Complex.re_add_im]
    rw [heq, inner_smul_right, real_inner_self_eq_norm_sq, L08_norm_unitCircle]
    ring
  have hflux := discEnergy_integral_divergence_smooth hF
  rw [intervalIntegral.integral_congr (fun θ _ => hboundary θ)] at hflux
  have hidentity : (∫ z in Metric.ball (0 : ℂ) 1, D z) =
      ∫ θ in (-Real.pi)..Real.pi, u (L08_unitCircle θ) ^ 2 :=
    (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv).symm.trans hflux
  have hbound (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      D z ≤ 3 * u z ^ 2 + discEnergyRealGradientSq u z := by
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hxy : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
      have hn : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
      simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq] using hn
    let a := discEnergyPartial u 1 z
    let b := discEnergyPartial u Complex.I z
    have hnorm : (z.re * a + z.im * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
      have h0 : 0 ≤ (1 - z.re ^ 2 - z.im ^ 2) * (a ^ 2 + b ^ 2) :=
        mul_nonneg (by linarith) (add_nonneg (sq_nonneg a) (sq_nonneg b))
      nlinarith [sq_nonneg (z.re * b - z.im * a)]
    change 2 * (u z ^ 2 + u z * (z.re * a + z.im * b)) ≤
      3 * u z ^ 2 + (a ^ 2 + b ^ 2)
    nlinarith [sq_nonneg (u z - (z.re * a + z.im * b))]
  have hDc : ContinuousOn D (Metric.closedBall (0 : ℂ) 1) :=
    continuousOn_const.mul ((hu.continuousOn.pow 2).add (hu.continuousOn.mul
      ((Complex.continuous_re.continuousOn.mul (discEnergyPartial_contDiffOn hu 1).continuousOn).add
        (Complex.continuous_im.continuousOn.mul (discEnergyPartial_contDiffOn hu Complex.I).continuousOn))))
  have hU := discEnergy_integrableOn (hu.continuousOn.pow 2)
  change IntegrableOn (fun z => u z ^ 2) (Metric.ball (0 : ℂ) 1) at hU
  have hG := discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hu)
  have hle := integral_mono_ae (discEnergy_integrableOn hDc) ((hU.const_mul 3).add hG) (by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hbound z hz)
  simp only [Pi.add_apply] at hle
  rw [hidentity, integral_add (hU.const_mul 3) hG, integral_const_mul] at hle
  exact hle

end Yau.Blueprint.V02Proof
