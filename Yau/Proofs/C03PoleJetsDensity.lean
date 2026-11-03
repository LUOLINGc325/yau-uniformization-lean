import Yau.Geometry.Basic
import Mathlib

/-! Actual critical pole density and its shrinking-ball L2 comparison. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Yau.Proofs.C03Aux.PoleJets

open Yau
variable {n : ℕ}

def weightedDensity (p : ℕ) (f : ComplexVector n → ℂ) (z : ComplexVector n) : ℝ :=
  ‖f z‖ ^ 2 * (‖z‖ ^ p)⁻¹

theorem weightedDensity_nonneg (p : ℕ) (f : ComplexVector n → ℂ) (z : ComplexVector n) :
    0 ≤ weightedDensity p f z := by unfold weightedDensity; positivity

theorem critical_density_rpow (f : ComplexVector n → ℂ) (z : ComplexVector n) :
    weightedDensity (2 * (n + 1)) f z =
      ‖f z‖ ^ 2 * ‖z‖ ^ (-2 * ((n : ℝ) + 1)) := by
  have he : -2 * ((n : ℝ) + 1) = -((2 * (n + 1) : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (norm_nonneg z), Real.rpow_natCast]
  rfl

theorem weightedDensity_measurable (p : ℕ) {f : ComplexVector n → ℂ} (hf : Continuous f) :
    Measurable (weightedDensity p f) :=
  (hf.norm.measurable.pow_const 2).mul ((measurable_norm.pow_const p).inv)

theorem integrableOn_weightedDensity (p : ℕ) {f : ComplexVector n → ℂ} (hf : Continuous f)
    {S : Set (ComplexVector n)}
    (hfinite : (∫⁻ z in S, ENNReal.ofReal (weightedDensity p f z)) < ∞) :
    IntegrableOn (weightedDensity p f) S volume := by
  exact ⟨(weightedDensity_measurable p hf).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (weightedDensity_nonneg p f))).mpr hfinite⟩

theorem weightedDensity_point_bound (p : ℕ) (f : ComplexVector n → ℂ)
    {z : ComplexVector n} (hz : z ≠ 0) {t : ℝ} (ht : ‖z‖ ≤ t) :
    ‖f z‖ ^ 2 ≤ t ^ p * weightedDensity p f z := by
  have hpow : ‖z‖ ^ p ≤ t ^ p := pow_le_pow_left₀ (norm_nonneg z) ht _
  calc
    _ = ‖z‖ ^ p * weightedDensity p f z := by
      unfold weightedDensity
      field_simp [pow_ne_zero p (norm_ne_zero_iff.mpr hz)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (weightedDensity_nonneg p f z)

theorem closedBall_L2_le_punctured_mass
    (hn : 1 ≤ n) (p : ℕ) (f : ComplexVector n → ℂ)
    (hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume)
    (R : ℝ) (hW : IntegrableOn (weightedDensity p f) (Metric.ball 0 R) volume)
    {t : ℝ} (ht : 0 < t) (htR : 2 * t < R) :
    (∫ z in Metric.closedBall (0 : ComplexVector n) t, ‖f z‖ ^ 2) ≤
      (2 * t) ^ p * ∫ z in Metric.ball (0 : ComplexVector n) (2 * t) \ {0}, weightedDensity p f z := by
  letI : NeZero n := ⟨by omega⟩
  let S := Metric.ball (0 : ComplexVector n) (2 * t) \ {0}
  have hS : MeasurableSet S := measurableSet_ball.diff (measurableSet_singleton 0)
  have hsubR : S ⊆ Metric.ball (0 : ComplexVector n) R :=
    fun _ hz => Metric.ball_subset_ball htR.le hz.1
  have hzero : ∀ᵐ z : ComplexVector n ∂volume, z ≠ 0 := by
    apply ae_iff.mpr
    simp
  have hsub : Metric.closedBall (0 : ComplexVector n) t ≤ᵐ[volume] S := by
    filter_upwards [hzero] with z hz
    intro hzt
    exact ⟨Metric.closedBall_subset_ball (by linarith) hzt, by simpa using hz⟩
  have hfi : IntegrableOn (fun z => ‖f z‖ ^ 2) S volume := hf2.integrableOn
  have hWi : IntegrableOn (weightedDensity p f) S volume := hW.mono_set hsubR
  calc
    _ ≤ ∫ z in S, ‖f z‖ ^ 2 :=
      setIntegral_mono_set hfi (Eventually.of_forall fun z => sq_nonneg ‖f z‖) hsub
    _ ≤ ∫ z in S, (2 * t) ^ p * weightedDensity p f z := by
      apply setIntegral_mono_on hfi (hWi.const_mul _) hS
      intro z hz
      apply weightedDensity_point_bound p f (by simpa using hz.2)
      have hnorm : ‖z‖ < 2 * t := by
        simpa only [Metric.mem_ball, dist_zero_right] using hz.1
      exact hnorm.le
    _ = _ := integral_const_mul _ _

end Yau.Proofs.C03Aux.PoleJets
