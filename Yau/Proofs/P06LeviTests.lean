import Yau.Proofs.P06Geometry

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux Yau.LeafProofs.L22Aux

def directionSecond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (v z : E) : ℝ := fderiv ℝ (fun w => fderiv ℝ f w v) z v

theorem direction_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (v : E) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) O :=
  (hf.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const

theorem directionSecond_eq_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v : E) :
    directionSecond f v z = fderiv ℝ (fderiv ℝ f) z v v := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [directionSecond, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem leviDirection_eq_second {n : ℕ} {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    leviDirection (leviC f z) v =
      (directionSecond f v z + directionSecond f (Complex.I • v) z) / 4 := by
  rw [leviDirection, leviC_quadratic_re hf v]
  rw [complexLeviQuadratic, directionSecond_eq_hessian hf, directionSecond_eq_hessian hf]

/-- Twice integrating by parts gives the actual self-adjoint constant
direction second derivative, for a compact test inside an open chart. -/
theorem integral_second_direction_test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {O : Set E} (hO : IsOpen O)
    {φ u : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hu : ContDiffOn ℝ ∞ u O) (v : E) :
    (∫ z, u z * directionSecond φ v z ∂μ) = ∫ z, φ z * directionSecond u v z ∂μ := by
  have hDφ : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDu := direction_contDiffOn hO hu v
  have h₁ := integral_compactTest_direction_on μ hO (hφ.of_le (by simp)) hcφ hφO
    (hDu.of_le (by simp)) v
  have h₂ := integral_compactTest_direction_on μ hO (hDφ.of_le (by simp))
    (hcφ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hφO)
    (hu.of_le (by simp)) v
  rw [h₂, neg_neg] at h₁
  simpa only [directionSecond, mul_comm] using h₁.symm

/-- The distributional constant-direction Levi test has exactly the
classical Levi pairing for smooth data; the chart cutoff is literal. -/
theorem integral_leviDirection_test {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {φ u : ComplexVector n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hu : ContDiffOn ℝ ∞ u O) (v : ComplexVector n) :
    (∫ z, u z * leviDirection (leviC φ z) v ∂lebesgueC n) =
      ∫ z, φ z * leviDirection (leviC u z) v ∂lebesgueC n := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  have hDφ (w : ComplexVector n) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z w) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDDφ (w : ComplexVector n) : Continuous (directionSecond φ w) :=
    (((hDφ w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hleft (w : ComplexVector n) : Integrable (fun z => u z * directionSecond φ w z) (lebesgueC n) := by
    have hi := integrable_compactTest_mul (lebesgueC n) hO (hDDφ w)
      ((hcφ.fderiv_apply ℝ w).fderiv_apply ℝ w)
      ((tsupport_fderiv_apply_subset ℝ w).trans ((tsupport_fderiv_apply_subset ℝ w).trans hφO)) hu.continuousOn
    simpa only [mul_comm] using hi
  have hright (w : ComplexVector n) : Integrable (fun z => φ z * directionSecond u w z) (lebesgueC n) :=
    integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO
      (direction_contDiffOn hO (direction_contDiffOn hO hu w) w).continuousOn
  have heL : (fun z => u z * leviDirection (leviC φ z) v) =
      (fun z => (u z * directionSecond φ v z + u z * directionSecond φ (Complex.I • v) z) / 4) := by
    funext z
    rw [leviDirection_eq_second (hφ.contDiffAt.of_le (by simp)) v]
    ring
  have heR : (fun z => φ z * leviDirection (leviC u z) v) =
      (fun z => (φ z * directionSecond u v z + φ z * directionSecond u (Complex.I • v) z) / 4) := by
    funext z
    by_cases hz : z ∈ O
    · rw [leviDirection_eq_second ((hu.contDiffAt (hO.mem_nhds hz)).of_le (by simp)) v]
      ring
    · have hzφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hzφ, zero_mul, add_zero, zero_div]
  rw [heL, heR, integral_div, integral_div,
    integral_add (hleft v) (hleft (Complex.I • v)), integral_add (hright v) (hright (Complex.I • v)),
    integral_second_direction_test (lebesgueC n) hO hφ hcφ hφO hu v,
    integral_second_direction_test (lebesgueC n) hO hφ hcφ hφO hu (Complex.I • v)]

end Yau.NodeProofs.P06Aux
