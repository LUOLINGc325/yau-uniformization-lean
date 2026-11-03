import Yau.Proofs.Y03DualPullback

/-! The exact holomorphic cotangent/time curve, including both factors of two. -/

open scoped Topology ContDiff Matrix

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

def stripCovector (μ : Fin n → ℝ) (a : ComplexVector n) (z : ℂ) : ComplexVector n :=
  WithLp.toLp 2 (fun i => a i * Complex.exp (((-μ i / 2 : ℝ) : ℂ) * z))

def metricStripCurve (x₀ : ComplexVector n) (P : Herm n) (t : ℝ)
    (μ : Fin n → ℝ) (a : ComplexVector n) (z : ℂ) : ComplexVector n × ComplexVector n × ℂ :=
  (x₀, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P⁻¹).transpose (stripCovector μ a z),
    ((Real.log t : ℂ) + z) / 2)

theorem stripCovector_contDiff (μ : Fin n → ℝ) (a : ComplexVector n) :
    ContDiff ℂ ∞ (stripCovector μ a) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℂ ∞ (fun z => a i * Complex.exp (((-μ i / 2 : ℝ) : ℂ) * z))
  fun_prop

theorem metricStripCurve_contDiff (x₀ : ComplexVector n) (P : Herm n) (t : ℝ)
    (μ : Fin n → ℝ) (a : ComplexVector n) : ContDiff ℂ ∞ (metricStripCurve x₀ P t μ a) := by
  unfold metricStripCurve
  exact contDiff_const.prodMk (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (P⁻¹).transpose).contDiff.comp
    (stripCovector_contDiff μ a)).prodMk (by fun_prop))

theorem metricStripCurve_time (x₀ : ComplexVector n) (P : Herm n) {t : ℝ} (ht : 0 < t)
    (μ : Fin n → ℝ) (a : ComplexVector n) (z : ℂ) :
    Real.exp (2 * (metricStripCurve x₀ P t μ a z).2.2.re) = t * Real.exp z.re := by
  have heq : 2 * (metricStripCurve x₀ P t μ a z).2.2.re = Real.log t + z.re := by
    simp [metricStripCurve, Complex.add_re]
    ring
  rw [heq, Real.exp_add, Real.exp_log ht]

theorem stripCovector_norm_sq (μ : Fin n → ℝ) (a : ComplexVector n) (z : ℂ) (i : Fin n) :
    ‖stripCovector μ a z i‖ ^ 2 = ‖a i‖ ^ 2 * Real.exp (-μ i * z.re) := by
  change ‖a i * Complex.exp (((-μ i / 2 : ℝ) : ℂ) * z)‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_exp]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  congr 1
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem dualNormMat_diagonal (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (ξ : ComplexVector n) :
    dualNormMat (Matrix.diagonal (fun i => (d i : ℂ))) ξ = ∑ i, ‖ξ i‖ ^ 2 / d i := by
  have hleft : Matrix.diagonal (fun i => ((d i)⁻¹ : ℝ) : Fin n → ℂ) *
      Matrix.diagonal (fun i => (d i : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hd]
  have hinv := Matrix.inv_eq_left_inv hleft
  unfold dualNormMat
  rw [hinv, Matrix.diagonal_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  change Complex.reCLM (∑ i, star (WithLp.ofLp ξ) i * ((((d i)⁻¹ : ℝ) : ℂ) * WithLp.ofLp ξ i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.reCLM_apply, Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero, Complex.sq_norm, Complex.normSq_apply, div_eq_mul_inv]
  ring

theorem stripCovector_diagonal_boundary (μ : Fin n → ℝ) (a : ComplexVector n) (T : ℝ)
    (z : ℂ) (hz : z.re = T) :
    dualNormMat (Matrix.diagonal (fun i => (Real.exp (-μ i * T) : ℂ))) (stripCovector μ a z) =
      ∑ i, ‖a i‖ ^ 2 := by
  rw [dualNormMat_diagonal _ (fun i => ne_of_gt (Real.exp_pos _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [stripCovector_norm_sq, hz, mul_div_cancel_right₀ _ (ne_of_gt (Real.exp_pos _))]

end Yau.Blueprint.Alignment.Y03Proof
