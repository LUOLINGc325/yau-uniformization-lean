import Yau.Proofs.C03EnvelopeSmoothingKernel

/-! Fubini for the actual normalized kernel preserves a fixed circle correction exactly. -/
noncomputable section
open scoped Topology ContDiff Convolution
open MeasureTheory Set Metric ContinuousLinearMap
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem integrable_kernel_circle_product
    (φ : ContDiffBump (0 : ComplexVector n)) (F : ComplexVector n → ℝ)
    (hF : Continuous F) (z w : ComplexVector n) :
    Integrable (fun p : ComplexVector n × ℝ =>
      φ.normed volume p.1 * F (z + Complex.exp (p.2 * Complex.I) • w - p.1))
      ((volume.restrict (closedBall (0 : ComplexVector n) φ.rOut)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  rw [Measure.prod_restrict]
  have hangle : Continuous (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by fun_prop
  have hpath : Continuous (fun p : ComplexVector n × ℝ =>
      z + Complex.exp (p.2 * Complex.I) • w - p.1) :=
    ((continuous_complex_affine z w).comp (hangle.comp continuous_snd)).sub continuous_fst
  have hc : Continuous (fun p : ComplexVector n × ℝ =>
      φ.normed volume p.1 * F (z + Complex.exp (p.2 * Complex.I) • w - p.1)) :=
    (φ.continuous_normed.comp continuous_fst).mul (hF.comp hpath)
  exact (hc.continuousOn.integrableOn_compact
    ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
      (Set.prod_mono Subset.rfl Ioc_subset_Icc_self)

theorem normalizedConvolution_circle_correction
    (φ : ContDiffBump (0 : ComplexVector n)) (F : ComplexVector n → ℝ)
    (hF : Continuous F) (z w : ComplexVector n) (A : ℝ)
    (hcircle : ∀ a ∈ closedBall (0 : ComplexVector n) φ.rOut,
      F (z - a) + A ≤
        circleAverage (fun θ => F (z + Complex.exp (θ * Complex.I) • w - a))) :
    normalizedConvolution φ F z + A ≤
      circleAverage (fun θ => normalizedConvolution φ F (z + Complex.exp (θ * Complex.I) • w)) := by
  let B : Set (ComplexVector n) := closedBall 0 φ.rOut
  have hprod := integrable_kernel_circle_product φ F hF z w
  have hmean : Integrable (fun a => circleAverage (fun θ =>
      φ.normed volume a * F (z + Complex.exp (θ * Complex.I) • w - a)))
      (volume.restrict B) := by
    simpa only [circleAverage, intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
      hprod.integral_prod_left.const_mul ((2 * Real.pi)⁻¹)
  have hleft : (∫ a in B, φ.normed volume a * (F (z - a) + A)) =
      normalizedConvolution φ F z + A := by
    simp_rw [mul_add]
    rw [integral_add (integrable_normalizedKernel_at φ F hF z).integrableOn
      ((normalizedKernel_integrable φ).mul_const A).integrableOn,
      integral_mul_const, normalizedKernel_closed_integral, one_mul,
      ← normalizedConvolution_eq_setIntegral]
  have hright : (∫ a in B, circleAverage (fun θ =>
      φ.normed volume a * F (z + Complex.exp (θ * Complex.I) • w - a))) =
      circleAverage (fun θ => normalizedConvolution φ F (z + Complex.exp (θ * Complex.I) • w)) := by
    rw [integral_circleAverage (volume.restrict B)
      (F := fun a theta => φ.normed volume a * F (z + Complex.exp (theta * Complex.I) • w - a)) hprod]
    apply congrArg circleAverage
    funext θ
    exact (normalizedConvolution_eq_setIntegral φ F _).symm
  have hle : (∫ a in B, φ.normed volume a * (F (z - a) + A)) ≤
      ∫ a in B, circleAverage (fun θ =>
        φ.normed volume a * F (z + Complex.exp (θ * Complex.I) • w - a)) := by
    apply integral_mono_ae
      (integrable_normalizedKernel_at φ (fun y => F y + A) (hF.add continuous_const) z).integrableOn
      hmean
    filter_upwards [ae_restrict_mem (isClosed_closedBall.measurableSet)] with a ha
    rw [circleAverage_smul]
    exact mul_le_mul_of_nonneg_left (hcircle a ha) (φ.nonneg_normed a)
  rw [hleft, hright] at hle
  exact hle

end Yau.Proofs.C03Aux.EnvelopeSmoothing

