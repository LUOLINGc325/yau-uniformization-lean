import Yau.LeafProofs.L22Second
import Yau.LeafProofs.L22LeviBasic
import Yau.LeafProofs.L08

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder
open MeasureTheory Set Filter

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem circleAverage_cos_sq : circleAverage (fun θ => Real.cos θ ^ 2) = 1 / 2 := by
  unfold circleAverage
  rw [integral_cos_sq]
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, mul_zero, sub_zero, zero_add, sub_self]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem circleAverage_sin_sq : circleAverage (fun θ => Real.sin θ ^ 2) = 1 / 2 := by
  unfold circleAverage
  rw [integral_sin_sq]
  simp only [Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero, Real.sin_zero,
    one_mul, zero_mul, mul_zero, sub_zero, zero_add, sub_self]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem circleAverage_sin_mul_cos :
    circleAverage (fun θ => Real.sin θ * Real.cos θ) = 0 := by
  unfold circleAverage
  rw [integral_sin_mul_cos₁]
  simp

/-- The angular mean of a real bilinear form on a complex line is half its
real trace on that line. All cross terms are integrated explicitly. -/
theorem circleAverage_bilinear (B : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ)
    (v : ComplexVector n) :
    circleAverage (fun θ => B (Complex.exp (θ * Complex.I) • v)
      (Complex.exp (θ * Complex.I) • v)) =
      (B v v + B (Complex.I • v) (Complex.I • v)) / 2 := by
  have hv (θ : ℝ) : Complex.exp (θ * Complex.I) • v =
      Real.cos θ • v + Real.sin θ • (Complex.I • v) := by
    rw [Complex.exp_ofReal_mul_I, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have heq : (fun θ : ℝ => B (Complex.exp (θ * Complex.I) • v)
      (Complex.exp (θ * Complex.I) • v)) =
      (fun θ => B v v * Real.cos θ ^ 2 +
        B (Complex.I • v) (Complex.I • v) * Real.sin θ ^ 2 +
        (B v (Complex.I • v) + B (Complex.I • v) v) * (Real.sin θ * Real.cos θ)) := by
    funext θ
    rw [hv]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [heq, circleAverage_add (by fun_prop) (by fun_prop),
    circleAverage_add (by fun_prop) (by fun_prop), circleAverage_smul,
    circleAverage_smul, circleAverage_smul, circleAverage_cos_sq,
    circleAverage_sin_sq, circleAverage_sin_mul_cos]
  ring

def angularLineMean (f : ComplexVector n → ℝ) (z v : ComplexVector n) (r : ℝ) : ℝ :=
  circleAverage (fun θ => f (z + r • (Complex.exp (θ * Complex.I) • v)))

theorem hasDerivAt_angularLineMean {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ ∞ f) (z v : ComplexVector n) (r : ℝ) :
    HasDerivAt (angularLineMean f z v)
      (circleAverage (fun θ => fderiv ℝ f
        (z + r • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v))) r := by
  have hq : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I) • v) := by fun_prop
  have hpath : Continuous (fun p : ℝ × ℝ =>
      z + p.1 • (Complex.exp (p.2 * Complex.I) • v)) := by fun_prop
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  apply (L08_hasDerivAt_intervalIntegral (hf.continuous.comp hpath)
    ((hdf.comp hpath).clm_apply (hq.comp continuous_snd))
    (fun s θ => ?_) 0 (2 * Real.pi) r).const_mul ((2 * Real.pi)⁻¹)
  convert (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const (Complex.exp (θ * Complex.I) • v)).const_add z) using 1 <;>
    simp only [Function.comp_def, id_eq, one_smul]

theorem hasDerivAt_angularLineMean_derivative {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ ∞ f) (z v : ComplexVector n) (r : ℝ) :
    HasDerivAt
      (fun s => circleAverage (fun θ => fderiv ℝ f
        (z + s • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v)))
      (circleAverage (fun θ => fderiv ℝ (fderiv ℝ f)
        (z + r • (Complex.exp (θ * Complex.I) • v))
        (Complex.exp (θ * Complex.I) • v) (Complex.exp (θ * Complex.I) • v))) r := by
  have hq : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I) • v) := by fun_prop
  have hpath : Continuous (fun p : ℝ × ℝ =>
      z + p.1 • (Complex.exp (p.2 * Complex.I) • v)) := by fun_prop
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hqc : Continuous (fun p : ℝ × ℝ => Complex.exp (p.2 * Complex.I) • v) :=
    hq.comp continuous_snd
  apply (L08_hasDerivAt_intervalIntegral
    ((hdf.continuous.comp hpath).clm_apply hqc)
    (((hdf.continuous_fderiv (by simp)).comp hpath).clm_apply hqc |>.clm_apply hqc)
    (fun s θ => ?_) 0 (2 * Real.pi) r).const_mul ((2 * Real.pi)⁻¹)
  have hd := (hdf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const (Complex.exp (θ * Complex.I) • v)).const_add z)
  convert hd.clm_apply (hasDerivAt_const s (Complex.exp (θ * Complex.I) • v)) using 1 <;>
    simp only [Function.comp_def, id_eq, one_smul, ContinuousLinearMap.map_zero, add_zero]

theorem second_deriv_angularLineMean {f : ComplexVector n → ℝ}
    (hf : ContDiff ℝ ∞ f) (z v : ComplexVector n) :
    deriv (deriv (angularLineMean f z v)) 0 =
      (fderiv ℝ (fderiv ℝ f) z v v +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v)) / 2 := by
  have heq : deriv (angularLineMean f z v) =
      (fun r => circleAverage (fun θ => fderiv ℝ f
        (z + r • (Complex.exp (θ * Complex.I) • v)) (Complex.exp (θ * Complex.I) • v))) :=
    funext (fun r => (hasDerivAt_angularLineMean hf z v r).deriv)
  rw [heq, (hasDerivAt_angularLineMean_derivative hf z v 0).deriv]
  simp only [zero_smul, add_zero]
  exact circleAverage_bilinear _ _

theorem angularLineMean_zero (f : ComplexVector n → ℝ) (z v : ComplexVector n) :
    angularLineMean f z v 0 = f z := by
  simp only [angularLineMean, zero_smul, add_zero, circleAverage_const]

/-- Necessity of nonnegative complex Hessian trace follows from the frozen
disc-submean predicate by taking a local minimum of the genuine angular mean. -/
theorem complexHessianTrace_nonneg_of_smooth_psh
    {O : Set (ComplexVector n)} {f : ComplexVector n → ℝ}
    (hO : IsOpen O) (hf : LeafCandidates.ComplexLinePshOn O f)
    (hs : ContDiff ℝ ∞ f) {z : ComplexVector n} (hz : z ∈ O) (v : ComplexVector n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) z v v +
      fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v) := by
  obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO z hz
  let δ : ℝ := R / (‖v‖ + 1)
  have hden : 0 < ‖v‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hR hden
  have hmin : IsLocalMin (angularLineMean f z v) 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
    rw [angularLineMean_zero]
    have hr' : |r| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hr
    have hsmall : |r| * (‖v‖ + 1) < R := by
      exact (mul_lt_mul_of_pos_right hr' hden).trans_eq (div_mul_cancel₀ R hden.ne')
    have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • (r • v) ∈ O := by
      intro ζ hζ
      apply hRO
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul,
        Real.norm_eq_abs]
      calc
        ‖ζ‖ * (|r| * ‖v‖) ≤ |r| * ‖v‖ :=
          mul_le_of_le_one_left (by positivity) hζ
        _ ≤ |r| * (‖v‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg r)
        _ < R := hsmall
    have hsub := hf.2 z (r • v) hdisc
    simpa only [angularLineMean, smul_comm r] using hsub
  have hnonneg := second_deriv_nonneg_of_localMin hmin
    (hasDerivAt_angularLineMean hs z v 0).continuousAt
  rw [second_deriv_angularLineMean hs z v] at hnonneg
  linarith

theorem leviC_posSemidef_of_smooth_psh
    {O : Set (ComplexVector n)} {f : ComplexVector n → ℝ}
    (hO : IsOpen O) (hf : LeafCandidates.ComplexLinePshOn O f)
    (hs : ContDiff ℝ ∞ f) {z : ComplexVector n} (hz : z ∈ O) :
    (leviC f z).PosSemidef := by
  apply (leviC_posSemidef_iff (hs.contDiffAt.of_le (by simp))).mpr
  intro v
  exact div_nonneg (complexHessianTrace_nonneg_of_smooth_psh hO hf hs hz v) (by norm_num)

end Yau.LeafProofs.L22Aux
