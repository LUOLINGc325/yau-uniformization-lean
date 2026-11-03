import Yau.LeafProofs.L10DiscMirandaFlux

/-! Two genuine circle derivatives of the zero boundary condition give
the curvature term and the nonnegative cofactor-Hessian flux. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs

theorem discMiranda_tangent_zero {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) (θ : ℝ) :
    -(L08_unitCircle θ).im * discEnergyPartial u 1 (L08_unitCircle θ) +
      (L08_unitCircle θ).re * discEnergyPartial u Complex.I (L08_unitCircle θ) = 0 := by
  have heq : (fun t => u (L08_unitCircle t)) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    exact hzero _ (by simpa [Metric.mem_sphere, dist_zero_right] using L08_norm_unitCircle t)
  have hz : HasDerivAt (fun t => u (L08_unitCircle t)) 0 θ := by
    rw [heq]
    exact hasDerivAt_const θ 0
  exact (discMiranda_circle_derivative hu θ).unique hz

theorem discMiranda_circle_curvature {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) (θ : ℝ) :
    (L08_unitCircle θ).im ^ 2 * discEnergyPartial (discEnergyPartial u 1) 1 (L08_unitCircle θ) -
      2 * (L08_unitCircle θ).re * (L08_unitCircle θ).im *
        discEnergyPartial (discEnergyPartial u 1) Complex.I (L08_unitCircle θ) +
      (L08_unitCircle θ).re ^ 2 * discEnergyPartial (discEnergyPartial u Complex.I) Complex.I (L08_unitCircle θ) =
    (L08_unitCircle θ).re * discEnergyPartial u 1 (L08_unitCircle θ) +
      (L08_unitCircle θ).im * discEnergyPartial u Complex.I (L08_unitCircle θ) := by
  let p := discEnergyPartial u 1
  let q := discEnergyPartial u Complex.I
  have hp : ContDiffOn ℝ ∞ p (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu 1
  have hq : ContDiffOn ℝ ∞ q (Metric.closedBall (0 : ℂ) 1) := discEnergyPartial_contDiffOn hu Complex.I
  have hx : HasDerivAt (fun t => (L08_unitCircle t).re) (-(L08_unitCircle θ).im) θ := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.mul_I_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (L08_hasDerivAt_unitCircle θ)
  have hy : HasDerivAt (fun t => (L08_unitCircle t).im) (L08_unitCircle θ).re θ := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.mul_I_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (L08_hasDerivAt_unitCircle θ)
  have hP := discMiranda_circle_derivative hp θ
  have hQ := discMiranda_circle_derivative hq θ
  have hd := (hy.neg.mul hP).add (hx.mul hQ)
  have heq : (fun t => -(L08_unitCircle t).im * p (L08_unitCircle t) +
      (L08_unitCircle t).re * q (L08_unitCircle t)) = fun _ : ℝ => (0 : ℝ) :=
    funext (discMiranda_tangent_zero hu hzero)
  have h0 : HasDerivAt (fun t => -(L08_unitCircle t).im * p (L08_unitCircle t) +
      (L08_unitCircle t).re * q (L08_unitCircle t)) 0 θ := by
    rw [heq]
    exact hasDerivAt_const θ 0
  have hs := hd.unique h0
  have hzK : L08_unitCircle θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, L08_norm_unitCircle]
  have hm : discEnergyPartial p Complex.I (L08_unitCircle θ) =
      discEnergyPartial q 1 (L08_unitCircle θ) := discMiranda_partial_commute hu 1 Complex.I hzK
  simp only [Pi.neg_apply] at hs
  rw [← hm] at hs
  change (L08_unitCircle θ).im ^ 2 * discEnergyPartial p 1 (L08_unitCircle θ) -
    2 * (L08_unitCircle θ).re * (L08_unitCircle θ).im * discEnergyPartial p Complex.I (L08_unitCircle θ) +
    (L08_unitCircle θ).re ^ 2 * discEnergyPartial q Complex.I (L08_unitCircle θ) =
    (L08_unitCircle θ).re * p (L08_unitCircle θ) + (L08_unitCircle θ).im * q (L08_unitCircle θ)
  linear_combination hs

theorem discMiranda_boundary_flux_algebra (x y p q a b d : ℝ)
    (hunit : x ^ 2 + y ^ 2 = 1) (htan : -y * p + x * q = 0)
    (hcurv : y ^ 2 * a - 2 * x * y * b + x ^ 2 * d = x * p + y * q) :
    x * (d * p - b * q) + y * (a * q - b * p) = (x * p + y * q)^2 := by
  let r := x * p + y * q
  have hp : p = r * x := by dsimp [r]; linear_combination -p * hunit - y * htan
  have hq : q = r * y := by dsimp [r]; linear_combination -q * hunit + x * htan
  calc
    _ = r * (y ^ 2 * a - 2 * x * y * b + x ^ 2 * d) := by rw [hp, hq]; ring
    _ = _ := by rw [hcurv]; dsimp [r]; ring

theorem discMirandaFlux_circle {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.closedBall (0 : ℂ) 1))
    (hzero : ∀ z ∈ Metric.sphere (0 : ℂ) 1, u z = 0) (θ : ℝ) :
    inner ℝ (L08_unitCircle θ) (discMirandaFlux u (L08_unitCircle θ)) =
      ((L08_unitCircle θ).re * discEnergyPartial u 1 (L08_unitCircle θ) +
        (L08_unitCircle θ).im * discEnergyPartial u Complex.I (L08_unitCircle θ))^2 := by
  have hn : (L08_unitCircle θ).re ^ 2 + (L08_unitCircle θ).im ^ 2 = 1 := by
    have h := Complex.sq_norm (L08_unitCircle θ)
    rw [L08_norm_unitCircle, one_pow] at h
    simpa [Complex.normSq_apply, pow_two] using h.symm
  have hzK : L08_unitCircle θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, L08_norm_unitCircle]
  have hm := discMiranda_partial_commute hu 1 Complex.I hzK
  have h := discMiranda_boundary_flux_algebra
    (L08_unitCircle θ).re (L08_unitCircle θ).im
    (discEnergyPartial u 1 (L08_unitCircle θ)) (discEnergyPartial u Complex.I (L08_unitCircle θ))
    (discEnergyPartial (discEnergyPartial u 1) 1 (L08_unitCircle θ))
    (discEnergyPartial (discEnergyPartial u 1) Complex.I (L08_unitCircle θ))
    (discEnergyPartial (discEnergyPartial u Complex.I) Complex.I (L08_unitCircle θ))
    hn (discMiranda_tangent_zero hu hzero θ) (discMiranda_circle_curvature hu hzero θ)
  simp only [Complex.inner, discMirandaFlux, discMirandaFluxRe, discMirandaFluxIm,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero] 
  rw [← hm]
  nlinarith [h]

end Yau.LeafProofs
