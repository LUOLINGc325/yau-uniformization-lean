import Yau.LeafProofs.L10DiscEnergyReal

/-! The zero-Dirichlet Poincaré inequality and the Green energy identity. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discEnergy_real_poincare {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, u z ^ 2) ≤
      ∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z := by
  let T : ℂ → ℝ := fun z => u z *
    (z.re * discEnergyPartial u 1 z + z.im * discEnergyPartial u Complex.I z)
  have hUc := hu.continuousOn.pow 2
  have hGc := discEnergyRealGradientSq_continuousOn hu
  have hTc : ContinuousOn T (Metric.closedBall (0 : ℂ) 1) :=
    hu.continuousOn.mul
      ((Complex.continuous_re.continuousOn.mul (discEnergyPartial_contDiffOn hu 1).continuousOn).add
        (Complex.continuous_im.continuousOn.mul (discEnergyPartial_contDiffOn hu Complex.I).continuousOn))
  have hpoint (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      -T z ≤ (u z ^ 2 + discEnergyRealGradientSq u z) / 2 := by
    have hz' : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hxy : z.re^2 + z.im^2 ≤ 1 := by
      have hn : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
      simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq] using hn
    let p := discEnergyPartial u 1 z
    let q := discEnergyPartial u Complex.I z
    have hnorm : (z.re * p + z.im * q)^2 ≤ p^2+q^2 := by
      have h0 : 0 ≤ (1 - z.re^2-z.im^2)*(p^2+q^2) :=
        mul_nonneg (by linarith only [hxy]) (add_nonneg (sq_nonneg p) (sq_nonneg q))
      nlinarith only [h0, sq_nonneg (z.re*q-z.im*p)]
    change -(u z * (z.re*p+z.im*q)) ≤ (u z^2+(p^2+q^2))/2
    nlinarith only [hnorm, sq_nonneg (u z + (z.re*p+z.im*q))]
  have hIntU : IntegrableOn (fun z => u z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn hUc
  have hIntG := discEnergy_integrableOn hGc
  have hIntT := discEnergy_integrableOn hTc
  have hle := integral_mono_ae hIntT.neg ((hIntU.add hIntG).div_const 2) (by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    exact hpoint z hz)
  simp only [Pi.neg_apply, Pi.add_apply] at hle
  rw [integral_neg, integral_div, integral_add hIntU hIntG] at hle
  have hidentity := discEnergy_real_radial_identity hu hzero
  change (∫ z in Metric.ball (0 : ℂ) 1, u z ^ 2) = -(∫ z in Metric.ball (0 : ℂ) 1, T z) at hidentity
  linarith only [hle, hidentity]

theorem discEnergy_real_green_identity {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z) =
      -(∫ z in Metric.ball (0 : ℂ) 1, u z * discEnergyRealLaplacian u z) := by
  let p := discEnergyPartial u (1 : ℂ)
  let q := discEnergyPartial u Complex.I
  have hp : ContDiffOn ℝ ∞ p (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu 1
  have hq : ContDiffOn ℝ ∞ q (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu Complex.I
  have hup : ContDiffOn ℝ ∞ (fun z => u z*p z) (Metric.closedBall (0 : ℂ) 1) := hu.mul hp
  have huq : ContDiffOn ℝ ∞ (fun z => u z*q z) (Metric.closedBall (0 : ℂ) 1) := hu.mul hq
  let F : ℂ → ℂ := fun z => ((u z*p z : ℝ) : ℂ) + ((u z*q z : ℝ) : ℂ)*Complex.I
  have hF : ContDiffOn ℝ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
    unfold F
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hup).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn huq).mul (contDiffOn_const (c := Complex.I)))
  have hdiv (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (fderiv ℝ F z 1).re + (fderiv ℝ F z Complex.I).im =
        discEnergyRealGradientSq u z + u z * discEnergyRealLaplacian u z := by
    have hdu := (discEnergy_contDiffAt hu hz).differentiableAt (by simp)
    have hdp := (discEnergy_contDiffAt hp hz).differentiableAt (by simp)
    have hdq := (discEnergy_contDiffAt hq hz).differentiableAt (by simp)
    change (fderiv ℝ (fun w => ((u w*p w : ℝ) : ℂ) + ((u w*q w : ℝ) : ℂ)*Complex.I) z 1).re +
      (fderiv ℝ (fun w => ((u w*p w : ℝ) : ℂ) + ((u w*q w : ℝ) : ℂ)*Complex.I) z Complex.I).im = _
    have hdup : DifferentiableAt ℝ (fun w => u w*p w) z := hdu.mul hdp
    have hduq : DifferentiableAt ℝ (fun w => u w*q w) z := hdu.mul hdq
    rw [discEnergy_coord_fderiv hdup hduq, discEnergy_coord_fderiv hdup hduq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
    rw [fderiv_fun_mul hdu hdp, fderiv_fun_mul hdu hdq]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← discEnergyPartial_eq_fderiv u 1 hz, ← discEnergyPartial_eq_fderiv u Complex.I hz,
      ← discEnergyPartial_eq_fderiv p 1 hz, ← discEnergyPartial_eq_fderiv q Complex.I hz]
    change u z * discEnergyPartial p 1 z + p z * p z +
      (u z * discEnergyPartial q Complex.I z + q z*q z) = _
    simp only [discEnergyRealGradientSq, discEnergyRealLaplacian, p, q]
    ring
  have hflux := discEnergy_integral_divergence_smooth hF
  have hboundary : (∫ θ in (-Real.pi)..Real.pi,
      inner ℝ (L08_unitCircle θ) (F (L08_unitCircle θ))) = 0 := by
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        have h0 := hzero (L08_unitCircle θ) (by simp [L08_norm_unitCircle])
        simp only [F, h0, zero_mul, Complex.ofReal_zero, add_zero, inner_zero_right]
      _ = 0 := by simp
  rw [hboundary] at hflux
  have hIntG : IntegrableOn (fun z => discEnergyRealGradientSq u z) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (discEnergyRealGradientSq_continuousOn hu)
  have hIntT : IntegrableOn (fun z => u z*discEnergyRealLaplacian u z) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hu.continuousOn.mul (discEnergyRealLaplacian_continuousOn hu))
  have heq := (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv).symm.trans hflux
  rw [integral_add hIntG hIntT] at heq
  linarith only [heq]

theorem discEnergy_real_first_order {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, u z ^ 2) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian u z)^2 ∧
      (∫ z in Metric.ball (0 : ℂ) 1, discEnergyRealGradientSq u z) ≤
        ∫ z in Metric.ball (0 : ℂ) 1, (discEnergyRealLaplacian u z)^2 := by
  have hP := discEnergy_real_poincare hu hzero
  have hG := discEnergy_real_green_identity hu hzero
  have hU : IntegrableOn (fun z => u z ^ 2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hu.continuousOn.pow 2)
  have hF : IntegrableOn (fun z => (discEnergyRealLaplacian u z)^2) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn ((discEnergyRealLaplacian_continuousOn hu).pow 2)
  have hT : IntegrableOn (fun z => u z*discEnergyRealLaplacian u z) (Metric.ball (0 : ℂ) 1) :=
    discEnergy_integrableOn (hu.continuousOn.mul (discEnergyRealLaplacian_continuousOn hu))
  have hle := integral_mono_ae hT.neg ((hU.add hF).div_const 2) (by
    filter_upwards with z
    change -(u z*discEnergyRealLaplacian u z) ≤
      (u z^2+(discEnergyRealLaplacian u z)^2)/2
    nlinarith only [sq_nonneg (u z+discEnergyRealLaplacian u z)])
  simp only [Pi.neg_apply, Pi.add_apply] at hle
  rw [integral_neg, integral_div, integral_add hU hF] at hle
  constructor <;> linarith only [hP, hG, hle]

end Yau.LeafProofs
