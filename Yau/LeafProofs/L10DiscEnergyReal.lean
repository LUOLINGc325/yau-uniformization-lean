import Yau.LeafProofs.L10DiscEnergyCalculus

/-! The real zero-Dirichlet energy identities on the closed unit disc. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace Yau.LeafProofs

def discEnergyRealGradientSq (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (discEnergyPartial u 1 z)^2 + (discEnergyPartial u Complex.I z)^2

def discEnergyRealLaplacian (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  discEnergyPartial (discEnergyPartial u 1) 1 z +
    discEnergyPartial (discEnergyPartial u Complex.I) Complex.I z

theorem discEnergy_integrableOn {f : ℂ → ℝ}
    (hf : ContinuousOn f (Metric.closedBall (0 : ℂ) 1)) :
    IntegrableOn f (Metric.ball (0 : ℂ) 1) :=
  (hf.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall

theorem discEnergyRealGradientSq_continuousOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyRealGradientSq u) (Metric.closedBall (0 : ℂ) 1) :=
  ((discEnergyPartial_contDiffOn hu 1).continuousOn.pow 2).add
    ((discEnergyPartial_contDiffOn hu Complex.I).continuousOn.pow 2)

theorem discEnergyRealLaplacian_continuousOn {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1)) :
    ContinuousOn (discEnergyRealLaplacian u) (Metric.closedBall (0 : ℂ) 1) :=
  ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu 1) 1).continuousOn).add
    ((discEnergyPartial_contDiffOn (discEnergyPartial_contDiffOn hu Complex.I) Complex.I).continuousOn)

/-- Coordinates of a real derivative in the orthonormal real basis. -/
theorem discEnergy_realCLM_coordinates (D : ℂ →L[ℝ] ℝ) (z : ℂ) :
    D z = z.re * D 1 + z.im * D Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  conv_lhs => rw [hz, map_add, map_smul, map_smul]
  rfl

theorem discEnergy_coord_fderiv {p q : ℂ → ℝ} {z : ℂ}
    (hp : DifferentiableAt ℝ p z) (hq : DifferentiableAt ℝ q z) (v : ℂ) :
    fderiv ℝ (fun w => (p w : ℂ) + (q w : ℂ) * Complex.I) z v =
      (fderiv ℝ p z v : ℂ) + (fderiv ℝ q z v : ℂ) * Complex.I := by
  have hpc := Complex.ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt
  have hqc := Complex.ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt
  have h := hpc.add (hqc.mul_const Complex.I)
  have heq := h.fderiv
  change fderiv ℝ (fun w => (p w : ℂ) + (q w : ℂ) * Complex.I) z = _ at heq
  simpa only [Complex.ofRealCLM_apply, add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, smul_eq_mul, mul_comm] using
    congrArg (fun D : ℂ →L[ℝ] ℂ => D v) heq

/-- The radial zero-boundary multiplier has zero total divergence. -/
theorem discEnergy_real_radial_identity {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) :
    (∫ z in Metric.ball (0 : ℂ) 1, u z ^ 2) =
      -(∫ z in Metric.ball (0 : ℂ) 1,
        u z * (z.re * discEnergyPartial u 1 z + z.im * discEnergyPartial u Complex.I z)) := by
  let p : ℂ → ℝ := fun z => u z ^ 2 * z.re
  let q : ℂ → ℝ := fun z => u z ^ 2 * z.im
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
        (fderiv ℝ (fun w => (p w : ℂ) + (q w : ℂ) * Complex.I) z Complex.I).im =
      2 * (u z ^ 2 + u z * (z.re * discEnergyPartial u 1 z +
        z.im * discEnergyPartial u Complex.I z)) := by
    have hdu := (discEnergy_contDiffAt hu hz).differentiableAt (by simp)
    rw [discEnergy_coord_fderiv ((discEnergy_contDiffAt hp hz).differentiableAt (by simp))
      ((discEnergy_contDiffAt hq hz).differentiableAt (by simp)),
      discEnergy_coord_fderiv ((discEnergy_contDiffAt hp hz).differentiableAt (by simp))
      ((discEnergy_contDiffAt hq hz).differentiableAt (by simp))]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add]
    simp only [p, q]
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
    rw [discEnergyPartial_eq_fderiv u 1 hz, discEnergyPartial_eq_fderiv u Complex.I hz]
    ring
  have hflux := discEnergy_integral_divergence_smooth hF
  have hboundary : (∫ θ in (-Real.pi)..Real.pi,
      inner ℝ (L08_unitCircle θ) ((p (L08_unitCircle θ) : ℂ) +
        (q (L08_unitCircle θ) : ℂ) * Complex.I)) = 0 := by
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        have h0 := hzero (L08_unitCircle θ) (by simp [L08_norm_unitCircle])
        simp only [p, q, h0, zero_pow (by norm_num : 2 ≠ 0), zero_mul, Complex.ofReal_zero,
          add_zero, inner_zero_right]
      _ = 0 := by simp
  rw [hboundary] at hflux
  have hIntU := discEnergy_integrableOn (hu.continuousOn.pow 2)
  have hIntT := discEnergy_integrableOn (hu.continuousOn.mul
    ((Complex.continuous_re.continuousOn.mul (discEnergyPartial_contDiffOn hu 1).continuousOn).add
      (Complex.continuous_im.continuousOn.mul (discEnergyPartial_contDiffOn hu Complex.I).continuousOn)))
  have heq := (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hdiv).symm.trans hflux
  have hIntU' : IntegrableOn (fun z => u z ^ 2) (Metric.ball (0 : ℂ) 1) := hIntU
  have hIntT' : IntegrableOn (fun z => u z * (z.re * discEnergyPartial u 1 z +
      z.im * discEnergyPartial u Complex.I z)) (Metric.ball (0 : ℂ) 1) := hIntT
  rw [integral_const_mul, integral_add hIntU' hIntT'] at heq
  linarith only [heq]

end Yau.LeafProofs
