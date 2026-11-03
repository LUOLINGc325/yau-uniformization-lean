import Yau.LeafProofs.L16TraceHeatPrimitive

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceAgeNorm_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceAgeNorm_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceAgeNorm_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceAgeNorm_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The true age derivative has uniformly bounded total variation. The Poisson
    part costs its actual probability mass; the tangent part uses the cancelled
    Gaussian Hessian estimate. This supplies triangle Fubini integrability. -/
theorem normalHeatAverage_age_norm_integral_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Space n → ℝ) (F H : ℝ),
      Continuous g → (∀ y, |g y| ≤ F) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ a : ℝ, 0 < a → ∀ t : ℝ, 0 < t →
      ∀ ξ : Space n,
      (∫ r in (0 : ℝ)..t, |-normalPoissonKernel a r*heatAverage r g ξ+
        normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ|) ≤ F+C*H*t^(α/2) := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα.le
  let d : ℝ := (Fintype.card (Yau.RIdx n) : ℝ)+1
  have hd : 0 < d := by dsimp only [d]; positivity
  refine ⟨d*C*(2/α),by positivity,?_⟩
  intro g F H hg hF hH0 hH a ha t ht ξ
  have hF0 : 0 ≤ F := (abs_nonneg (g 0)).trans (hF 0)
  have hProb := normalPoissonKernel_probability ha
  have hPInt : IntervalIntegrable (normalPoissonKernel a) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
    exact Integrable.mono_measure hProb.1
      (Measure.restrict_mono_set volume (fun _ hr => hr.1))
  have hMass : (∫ r in (0 : ℝ)..t, normalPoissonKernel a r) ≤ 1 := by
    rw [intervalIntegral.integral_of_le ht.le,integral_Ioc_eq_integral_Ioo,← hProb.2]
    apply setIntegral_mono_set hProb.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact normalPoissonKernel_nonneg ha.le hr
    · exact ae_of_all _ fun r hr => hr.1
  have hPowInt : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hPow : (∫ r in (0 : ℝ)..t, r^(α/2-1)) = (2/α)*t^(α/2) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,Real.zero_rpow (by linarith : α/2 ≠ 0),sub_zero]
    field_simp
  have hKI := (normalHeatAverage_integrated_heat_equation hα hg hF hH0 hH ha ht ξ).1
  have hPoint (r : ℝ) (hr : r ∈ Ioo 0 t) :
      |-normalPoissonKernel a r*heatAverage r g ξ+
        normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ| ≤
      normalPoissonKernel a r*F+(d*C*H)*r^(α/2-1) := by
    have hp0 := normalPoissonKernel_nonneg ha.le hr.1
    obtain ⟨hh0,hh1⟩ := normalHeatProfile_bounds hr.1 ha.le
    have hHA := heatAverage_bound hr.1 hg hF ξ
    have hHessian := hHess r hr.1 g F H hg hF hH0 hH ξ
    have hLap : |heatLaplacian (heatAverage r g) ξ| ≤ (d*C*H)*r^(α/2-1) := by
      calc
        _ ≤ (Fintype.card (Yau.RIdx n) : ℝ)*‖fderiv ℝ (fderiv ℝ (heatAverage r g)) ξ‖ :=
          heatLaplacian_abs_le _ _
        _ ≤ d*‖fderiv ℝ (fderiv ℝ (heatAverage r g)) ξ‖ := by
          exact mul_le_mul_of_nonneg_right (by dsimp only [d]; linarith) (norm_nonneg _)
        _ ≤ d*(C*H*r^(α/2-1)) := mul_le_mul_of_nonneg_left hHessian hd.le
        _ = _ := by ring
    calc
      _ ≤ |-normalPoissonKernel a r*heatAverage r g ξ|+
          |normalHeatProfile r a*heatLaplacian (heatAverage r g) ξ| := abs_add_le _ _
      _ = normalPoissonKernel a r*|heatAverage r g ξ|+
          normalHeatProfile r a*|heatLaplacian (heatAverage r g) ξ| := by
        rw [neg_mul,abs_neg,abs_mul,abs_of_nonneg hp0,abs_mul,abs_of_nonneg hh0]
      _ ≤ normalPoissonKernel a r*F+|heatLaplacian (heatAverage r g) ξ| :=
        add_le_add (mul_le_mul_of_nonneg_left hHA hp0) (mul_le_of_le_one_left (abs_nonneg _) hh1)
      _ ≤ _ := add_le_add_right hLap _
  calc
    _ ≤ ∫ r in (0 : ℝ)..t, normalPoissonKernel a r*F+(d*C*H)*r^(α/2-1) :=
      intervalIntegral.integral_mono_on_of_le_Ioo ht.le hKI.abs
        ((hPInt.mul_const F).add (hPowInt.const_mul (d*C*H))) hPoint
    _ = (∫ r in (0 : ℝ)..t, normalPoissonKernel a r)*F+(d*C*H)*((2/α)*t^(α/2)) := by
      rw [intervalIntegral.integral_add (hPInt.mul_const F) (hPowInt.const_mul (d*C*H)),
        intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,hPow]
    _ ≤ F+(d*C*(2/α))*H*t^(α/2) := by
      have hm := mul_le_mul_of_nonneg_right hMass hF0
      nlinarith

end Yau.LeafProofs.L16Aux
