import Yau.Proofs.C03EnvelopeSmoothingExtension
import Yau.LeafProofs.L22Circle

/-! The explicitly normalized convolution and its exact range bounds. -/
noncomputable section
open scoped Topology ContDiff Convolution
open MeasureTheory Set Metric ContinuousLinearMap
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

def normalizedConvolution (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) : ComplexVector n → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] F

theorem normalizedKernel_zero_outside (φ : ContDiffBump (0 : ComplexVector n))
    (a : ComplexVector n) (ha : a ∉ closedBall 0 φ.rOut) : φ.normed volume a = 0 := by
  have hn : a ∉ Function.support (φ.normed volume) := by
    rw [φ.support_normed_eq]
    exact fun hb => ha (ball_subset_closedBall hb)
  simpa only [Function.mem_support, not_not] using hn

theorem normalizedKernel_integrable (φ : ContDiffBump (0 : ComplexVector n)) :
    Integrable (φ.normed volume) volume :=
  φ.continuous_normed.integrable_of_hasCompactSupport φ.hasCompactSupport_normed

theorem normalizedKernel_closed_integral (φ : ContDiffBump (0 : ComplexVector n)) :
    (∫ a in closedBall (0 : ComplexVector n) φ.rOut, φ.normed volume a) = 1 := by
  calc
    (∫ a in closedBall (0 : ComplexVector n) φ.rOut, φ.normed volume a) =
        ∫ a, φ.normed volume a := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact fun a ha => normalizedKernel_zero_outside φ a ha
    _ = 1 := φ.integral_normed

theorem integrable_normalizedKernel_at (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) (hF : Continuous F) (z : ComplexVector n) :
    Integrable (fun a => φ.normed volume a * F (z - a)) volume :=
  (φ.continuous_normed.mul (hF.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport φ.hasCompactSupport_normed.mul_right

theorem normalizedConvolution_eq_setIntegral (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) (z : ComplexVector n) :
    normalizedConvolution φ F z =
      ∫ a in closedBall (0 : ComplexVector n) φ.rOut, φ.normed volume a * F (z - a) := by
  rw [normalizedConvolution, convolution_def]
  change (∫ a, φ.normed volume a * F (z - a)) = _
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro a ha
  rw [normalizedKernel_zero_outside φ a ha, zero_mul]

theorem normalizedConvolution_smooth (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) (hF : Continuous F) :
    ContDiff ℝ ∞ (normalizedConvolution φ F) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hF.locallyIntegrable

theorem normalizedConvolution_le (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) (hF : Continuous F) (z : ComplexVector n) (M : ℝ)
    (hbound : ∀ a ∈ closedBall (0 : ComplexVector n) φ.rOut, F (z - a) ≤ M) :
    normalizedConvolution φ F z ≤ M := by
  rw [normalizedConvolution, convolution_def]
  change (∫ a, φ.normed volume a * F (z - a)) ≤ M
  calc
    (∫ a, φ.normed volume a * F (z - a)) ≤ ∫ a, φ.normed volume a * M := by
      apply integral_mono (integrable_normalizedKernel_at φ F hF z)
        ((normalizedKernel_integrable φ).mul_const M)
      intro a
      change φ.normed volume a * F (z - a) ≤ φ.normed volume a * M
      by_cases ha : a ∈ closedBall (0 : ComplexVector n) φ.rOut
      · exact mul_le_mul_of_nonneg_left (hbound a ha) (φ.nonneg_normed a)
      · rw [normalizedKernel_zero_outside φ a ha, zero_mul, zero_mul]
    _ = M := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem normalizedConvolution_nonneg (φ : ContDiffBump (0 : ComplexVector n))
    (F : ComplexVector n → ℝ) (z : ComplexVector n)
    (hbound : ∀ a ∈ closedBall (0 : ComplexVector n) φ.rOut, 0 ≤ F (z - a)) :
    0 ≤ normalizedConvolution φ F z := by
  rw [normalizedConvolution, convolution_def]
  apply integral_nonneg
  intro a
  change 0 ≤ φ.normed volume a * F (z - a)
  by_cases ha : a ∈ closedBall (0 : ComplexVector n) φ.rOut
  · exact mul_nonneg (φ.nonneg_normed a) (hbound a ha)
  · rw [normalizedKernel_zero_outside φ a ha, zero_mul]

end Yau.Proofs.C03Aux.EnvelopeSmoothing

