import Yau.Proofs.Y03StripCurve
import Yau.Proofs.Y03MatrixInverseDerivative
import Yau.Proofs.Y03Endpoint

/-! Scalar quadratic forms retain the cotangent transpose convention exactly. -/

open scoped Topology Matrix
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def matrixForm (A : Herm n) (v : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

theorem dualNormMat_conj_eq_matrixForm (H : Herm n) (v : Fin n → ℂ) :
    dualNormMat H (WithLp.toLp 2 (star v)) = matrixForm H⁻¹ v := by
  unfold dualNormMat matrixForm
  simp only [star_star, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrixForm_diagonal (d : Fin n → ℝ) (v : Fin n → ℂ) :
    matrixForm (Matrix.diagonal (fun i => (d i : ℂ))) v = ∑ i, d i * ‖v i‖ ^ 2 := by
  unfold matrixForm
  simp only [Matrix.mulVec_diagonal, dotProduct]
  change Complex.reCLM (∑ i, star (v i) * ((d i : ℂ) * v i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.reCLM_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem matrixForm_hasDerivAt (A : ℝ → Herm n) (A' : Herm n) {x : ℝ}
    (hA : ∀ i j, HasDerivAt (fun y => A y i j) (A' i j) x) (v : Fin n → ℂ) :
    HasDerivAt (fun y => matrixForm (A y) v) (matrixForm A' v) x := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hA i j).const_mul (star (v i))).mul_const (v j)))
  convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd using 1
  · funext y
    simp only [matrixForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.reCLM_apply,
      Function.comp_apply, Pi.star_apply, Finset.sum_apply, mul_assoc]
  · simp only [matrixForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.reCLM_apply,
      Pi.star_apply, mul_assoc]

theorem exponential_form_hasDerivAt (μ : Fin n → ℝ) (v : Fin n → ℂ) (x : ℝ) :
    HasDerivAt (fun y => ∑ i, Real.exp (μ i * y) * ‖v i‖ ^ 2)
      (∑ i, μ i * Real.exp (μ i * x) * ‖v i‖ ^ 2) x := by
  have hterm (i : Fin n) : HasDerivAt (fun y => Real.exp (μ i * y) * ‖v i‖ ^ 2)
      (μ i * Real.exp (μ i * x) * ‖v i‖ ^ 2) x := by
    convert (((Real.hasDerivAt_exp (μ i * x)).comp x
      ((hasDerivAt_id x).const_mul (μ i))).mul_const (‖v i‖ ^ 2)) using 1
    · funext y; rfl
    · ring
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i) using 1
  funext y
  simp only [Finset.sum_apply]

theorem inverse_form_comparison_of_strip (H : ℝ → Herm n) (μ : Fin n → ℝ) (T : ℝ)
    (hstrip : ∀ a : ComplexVector n, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormMat (H z.re) (stripCovector μ a z) ≤ ∑ i, ‖a i‖ ^ 2)
    (v : Fin n → ℂ) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    matrixForm (H τ)⁻¹ v ≤ ∑ i, Real.exp (μ i * τ) * ‖v i‖ ^ 2 := by
  let a : ComplexVector n := WithLp.toLp 2 (fun i => star (v i) * (Real.exp (μ i * τ / 2) : ℂ))
  have heq : stripCovector μ a (τ : ℂ) = WithLp.toLp 2 (star v) := by
    ext i
    change star (v i) * (Real.exp (μ i * τ / 2) : ℂ) *
      Complex.exp (((-μ i / 2 : ℝ) : ℂ) * (τ : ℂ)) = star (v i)
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    have hz : μ i * τ / 2 + -μ i / 2 * τ = 0 := by ring
    rw [hz, Real.exp_zero, Complex.ofReal_one, mul_one]
  have hnorm (i : Fin n) : ‖a i‖ ^ 2 = Real.exp (μ i * τ) * ‖v i‖ ^ 2 := by
    change ‖star (v i) * (Real.exp (μ i * τ / 2) : ℂ)‖ ^ 2 = _
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    have hexp : μ i * τ / 2 + μ i * τ / 2 = μ i * τ := by ring
    rw [hexp, mul_comm]
  have hb := hstrip a (τ : ℂ) hτ.1 hτ.2
  rw [heq, dualNormMat_conj_eq_matrixForm] at hb
  simpa only [hnorm, Complex.ofReal_re] using hb

end Yau.Blueprint.Alignment.Y03Proof
