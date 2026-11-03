import Yau.Proofs.V02InfimumTest
import Yau.Proofs.V03LeviChain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Circle averages of the actual real Taylor polynomial. The quadratic
normalization is exactly one quarter of the real Laplacian. -/

open scoped Topology ContDiff
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

theorem parameterAverage_const (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]

theorem parameterAverage_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ => f θ + g θ) = circleAverage f + circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_add]

theorem parameterAverage_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ => f θ - g θ) = circleAverage f - circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), mul_sub]

theorem parameterAverage_mul (c : ℝ) (f : ℝ → ℝ) :
    circleAverage (fun θ => c * f θ) = c * circleAverage f := by
  unfold circleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem parameterAverage_sin : circleAverage Real.sin = 0 := by
  simp [circleAverage]

theorem parameterAverage_cos : circleAverage Real.cos = 0 := by
  simp [circleAverage]

theorem parameterAverage_sin_sq : circleAverage (fun θ => Real.sin θ ^ 2) = 1 / 2 := by
  unfold circleAverage
  rw [integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, Real.sin_two_pi, Real.cos_two_pi,
    mul_zero, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
  field_simp

theorem parameterAverage_cos_sq : circleAverage (fun θ => Real.cos θ ^ 2) = 1 / 2 := by
  unfold circleAverage
  rw [integral_cos_sq]
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, Real.sin_two_pi, Real.cos_two_pi,
    mul_zero, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
  field_simp

theorem parameterAverage_sin_cos :
    circleAverage (fun θ => Real.sin θ * Real.cos θ) = 0 := by
  unfold circleAverage
  rw [integral_sin_mul_cos₁]
  simp

theorem parameterCirclePoint_real_basis (ρ θ : ℝ) :
    (ρ : ℂ) * circlePoint θ =
      (ρ * Real.cos θ) • (1 : ℂ) + (ρ * Real.sin θ) • Complex.I := by
  simp only [circlePoint, Complex.exp_ofReal_mul_I, Complex.real_smul,
    Complex.ofReal_mul, mul_one]
  ring

theorem parameterCircle_quadratic_average (c : ℝ) (A : ℂ →L[ℝ] ℝ)
    (B : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ)) (ρ : ℝ) :
    circleAverage (fun θ =>
      c + A ((ρ : ℂ) * circlePoint θ) +
        (1 / 2 : ℝ) * B ((ρ : ℂ) * circlePoint θ) ((ρ : ℂ) * circlePoint θ)) =
      c + ρ ^ 2 / 4 * (B 1 1 + B Complex.I Complex.I) := by
  have heq : (fun θ => c + A ((ρ : ℂ) * circlePoint θ) +
      (1 / 2 : ℝ) * B ((ρ : ℂ) * circlePoint θ) ((ρ : ℂ) * circlePoint θ)) =
      fun θ => c + (ρ * A 1) * Real.cos θ + (ρ * A Complex.I) * Real.sin θ +
        (ρ ^ 2 / 2 * B 1 1) * Real.cos θ ^ 2 +
        (ρ ^ 2 / 2 * (B 1 Complex.I + B Complex.I 1)) * (Real.sin θ * Real.cos θ) +
        (ρ ^ 2 / 2 * B Complex.I Complex.I) * Real.sin θ ^ 2 := by
    funext θ
    rw [parameterCirclePoint_real_basis]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [heq]
  repeat' rw [parameterAverage_add (by fun_prop) (by fun_prop)]
  simp only [parameterAverage_mul, parameterAverage_const, parameterAverage_cos,
    parameterAverage_sin, parameterAverage_cos_sq, parameterAverage_sin_sq,
    parameterAverage_sin_cos]
  ring

theorem parameterCircle_secondTaylor_average {J : ℂ → ℝ}
    (hJ : ContDiffAt ℝ 2 J 0) (ρ : ℝ) :
    circleAverage (fun θ =>
      J 0 + fderiv ℝ J 0 ((ρ : ℂ) * circlePoint θ) + (1 / 2 : ℝ) *
        fderiv ℝ (fderiv ℝ J) 0 ((ρ : ℂ) * circlePoint θ) ((ρ : ℂ) * circlePoint θ)) =
      J 0 + ρ ^ 2 * V03Proof.mixedReal J := by
  rw [parameterCircle_quadratic_average]
  unfold V03Proof.mixedReal
  rw [V03Proof.mixedWirt_real_diagonal hJ]
  simp only [smul_eq_mul, mul_one]
  ring

end Yau.Blueprint.V02Proof
