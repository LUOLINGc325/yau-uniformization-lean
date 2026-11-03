import Yau.Proofs.Y03QuadraticForm

/-! Differentiate the genuine inverse-metric strip inequality at its two endpoints. -/

open scoped Topology Matrix
open Set Filter

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem inverse_exp_diagonal (μ : Fin n → ℝ) (T : ℝ) :
    (Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ)))⁻¹ =
      Matrix.diagonal (fun i => (Real.exp (μ i * T) : ℂ)) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext i
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have hz : μ i * T + -μ i * T = 0 := by ring
  rw [hz, Real.exp_zero, Complex.ofReal_one]

theorem matrixForm_one (v : Fin n → ℂ) : matrixForm (1 : Herm n) v = ∑ i, ‖v i‖ ^ 2 := by
  simpa only [Complex.ofReal_one, Matrix.diagonal_one, one_mul] using matrixForm_diagonal (fun _ => 1) v

theorem matrixForm_inverse_exp_diagonal (μ : Fin n → ℝ) (T : ℝ) (v : Fin n → ℂ) :
    matrixForm (Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ)))⁻¹ v =
      ∑ i, Real.exp (μ i * T) * ‖v i‖ ^ 2 := by
  rw [inverse_exp_diagonal, matrixForm_diagonal]

theorem inverse_metric_form_hasDerivAt (H : ℝ → Herm n) (R : Herm n) {x : ℝ}
    (hH : ∀ i j, HasDerivAt (fun y => H y i j) (-R i j) x)
    (hK : ∀ i j, DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) x)
    (hdet : ∀ᶠ y in 𝓝 x, IsUnit (H y).det) (v : Fin n → ℂ) :
    HasDerivAt (fun y => matrixForm (H y)⁻¹ v)
      (matrixForm ((H x)⁻¹ * R * (H x)⁻¹) v) x := by
  apply matrixForm_hasDerivAt
  have hd := matrix_inverse_entry_hasDerivAt H (-R) hH hK hdet
  simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, neg_neg] using hd

theorem inverse_form_left_endpoint (H : ℝ → Herm n) (R : Herm n) (μ : Fin n → ℝ)
    {T : ℝ} (hT : 0 < T) (hstart : H 0 = 1)
    (hstrip : ∀ a : ComplexVector n, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormMat (H z.re) (stripCovector μ a z) ≤ ∑ i, ‖a i‖ ^ 2)
    (hH : ∀ i j, HasDerivAt (fun y => H y i j) (-R i j) 0)
    (hK : ∀ i j, DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) 0)
    (hdet : ∀ᶠ y in 𝓝 (0 : ℝ), IsUnit (H y).det) (v : Fin n → ℂ) :
    matrixForm R v ≤ ∑ i, μ i * ‖v i‖ ^ 2 := by
  have hd := inverse_metric_form_hasDerivAt H R hH hK hdet v
  simp only [hstart, inv_one, Matrix.one_mul, Matrix.mul_one] at hd
  have heq : matrixForm (H 0)⁻¹ v = ∑ i, Real.exp (μ i * 0) * ‖v i‖ ^ 2 := by
    simp only [hstart, inv_one, matrixForm_one, mul_zero, Real.exp_zero, one_mul]
  have hb := left_endpoint_derivative_le hT
    (fun τ hτ => inverse_form_comparison_of_strip H μ T hstrip v hτ) heq hd
    (exponential_form_hasDerivAt μ v 0)
  simpa only [mul_zero, Real.exp_zero, mul_one] using hb

theorem inverse_form_right_endpoint (H : ℝ → Herm n) (R : Herm n) (μ : Fin n → ℝ)
    {T : ℝ} (hT : 0 < T)
    (hfinish : H T = Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ)))
    (hstrip : ∀ a : ComplexVector n, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormMat (H z.re) (stripCovector μ a z) ≤ ∑ i, ‖a i‖ ^ 2)
    (hH : ∀ i j, HasDerivAt (fun y => H y i j) (-R i j) T)
    (hK : ∀ i j, DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) T)
    (hdet : ∀ᶠ y in 𝓝 T, IsUnit (H y).det) (v : Fin n → ℂ) :
    (∑ i, μ i * Real.exp (μ i * T) * ‖v i‖ ^ 2) ≤
      matrixForm ((H T)⁻¹ * R * (H T)⁻¹) v := by
  have hd := inverse_metric_form_hasDerivAt H R hH hK hdet v
  have heq : matrixForm (H T)⁻¹ v = ∑ i, Real.exp (μ i * T) * ‖v i‖ ^ 2 := by
    rw [hfinish, matrixForm_inverse_exp_diagonal]
  exact right_endpoint_derivative_ge hT
    (fun τ hτ => inverse_form_comparison_of_strip H μ T hstrip v hτ) heq hd
    (exponential_form_hasDerivAt μ v T)

end Yau.Blueprint.Alignment.Y03Proof
