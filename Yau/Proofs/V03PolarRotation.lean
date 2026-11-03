import Yau.Proofs.V03LeviTwoForm

/-! The real Hessian trace in a complex line is invariant under rotation.
This is finite real bilinear algebra; no symmetry premise is needed. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem complex_real_expansion (v : ℂ) : v = v.re • (1 : ℂ) + v.im • Complex.I := by
  apply Complex.ext <;> simp [Complex.real_smul]

theorem complex_I_real_expansion (v : ℂ) :
    Complex.I * v = (-v.im) • (1 : ℂ) + v.re • Complex.I := by
  apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]

theorem real_bilinear_rotation_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (v : ℂ) :
    B v v + B (Complex.I * v) (Complex.I * v) =
      ‖v‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by
  have hn : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  conv_lhs => rw [complex_I_real_expansion, complex_real_expansion v]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hn]
  simp [Complex.real_smul]
  ring

theorem secondFDeriv_circle_rotation {u : ℂ → ℝ} (z v : ℂ) :
    fderiv ℝ (fderiv ℝ u) z v v +
      fderiv ℝ (fderiv ℝ u) z (Complex.I * v) (Complex.I * v) =
      ‖v‖ ^ 2 * (fderiv ℝ (fderiv ℝ u) z 1 1 +
        fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I) :=
  real_bilinear_rotation_trace _ v

end Yau.Blueprint.V03Proof
