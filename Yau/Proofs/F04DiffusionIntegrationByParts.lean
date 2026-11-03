import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L18Aux

/-- A compact smooth test makes multiplication by an actual locally C1
 coefficient globally C1. The zero germ supplies regularity outside its
 support, so the coefficient need not have a global smooth extension. -/
theorem compactTest_mul_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {O : Set E} (hO : IsOpen O) {η A : E → ℝ}
    (hη : ContDiff ℝ 1 η) (hηO : tsupport η ⊆ O)
    (hA : ContDiffOn ℝ 1 A O) : ContDiff ℝ 1 (fun x => η x * A x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · exact hη.contDiffAt.mul (hA.contDiffAt (hO.mem_nhds (hηO hx)))
  · have he : (fun x => η x * A x) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      change η y = 0 at hy
      rw [hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- Exact spatial integration by parts for a genuine variable coefficient
 and compact test. All coefficient drift is retained in the displayed
 derivative of A; no divergence-form replacement is assumed. -/
theorem integral_compactTest_coefficient_direction_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {O : Set E} (hO : IsOpen O) {η A f : E → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hA : ContDiffOn ℝ 1 A O) (hf : ContDiffOn ℝ 1 f O) (v : E) :
    (∫ x in O, η x * A x * fderiv ℝ f x v ∂μ) =
      -(∫ x in O, f x * (A x * fderiv ℝ η x v + fderiv ℝ A x v * η x) ∂μ) := by
  let θ := fun x => η x * A x
  have hθ : ContDiff ℝ 1 θ := compactTest_mul_contDiff hO hη hηO hA
  have hcθ : HasCompactSupport θ := hcη.mul_right
  have hθO : tsupport θ ⊆ O := tsupport_mul_subset_left.trans hηO
  have hL : (∫ x in O, θ x * fderiv ℝ f x v ∂μ) =
      ∫ x, θ x * fderiv ℝ f x v ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hθO hh)), zero_mul]
  have hR : (∫ x in O, fderiv ℝ θ x v * f x ∂μ) =
      ∫ x, fderiv ℝ θ x v * f x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hdO : tsupport (fun x => fderiv ℝ θ x v) ⊆ O :=
      (tsupport_fderiv_apply_subset ℝ v).trans hθO
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hdO hh)), zero_mul]
  have hIP := integral_compactTest_direction_on μ hO hθ hcθ hθO hf v
  rw [← hL, ← hR] at hIP
  change (∫ x in O, θ x * fderiv ℝ f x v ∂μ) = _
  rw [hIP]
  congr 1
  apply setIntegral_congr_fun hO.measurableSet
  intro x hx
  have hAx := (hA.contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
  change fderiv ℝ (fun y => η y * A y) x v * f x =
    f x * (A x * fderiv ℝ η x v + fderiv ℝ A x v * η x)
  rw [fderiv_fun_mul (hη.differentiable one_ne_zero x) hAx]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end Yau.F04Proof
