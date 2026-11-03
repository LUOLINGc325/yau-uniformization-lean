import Yau.Proofs.C05LeviTimeDerivative

/-! Linearity of the actual Levi matrix and complex Laplacian. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem secondFDeriv_add {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w + fderiv ℝ (fderiv ℝ g) z v w := by
  have he := congrArg (fun A => A ![v, w]) (iteratedFDeriv_add_apply hf hg)
  simpa only [Pi.add_def, iteratedFDeriv_two_apply, add_apply, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem secondFDeriv_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y => c * f y)) z v w =
      c * fderiv ℝ (fderiv ℝ f) z v w := by
  have he := congrArg (fun A => A ![v, w]) (iteratedFDeriv_const_smul_apply (a := c) hf)
  simpa only [Pi.smul_def, smul_eq_mul, iteratedFDeriv_two_apply,
    ContinuousMultilinearMap.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

set_option backward.isDefEq.respectTransparency false in
theorem leviC_add {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun y => f y + g y) z = leviC f z + leviC g z := by
  ext i j
  rw [Matrix.add_apply, leviC_eq_real_hessian (hf.add hg), leviC_eq_real_hessian hf,
    leviC_eq_real_hessian hg]
  simp_rw [secondFDeriv_add hf hg]
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
theorem leviC_const_mul {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    leviC (fun y => c * f y) z = (c : ℂ) • leviC f z := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, leviC_eq_real_hessian (contDiffAt_const.mul hf),
    leviC_eq_real_hessian hf]
  simp_rw [secondFDeriv_const_mul hf c]
  push_cast
  ring

theorem levi_add (f g : M.Carrier → ℝ) (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    levi (fun y => f y + g y) x = levi f x + levi g x := by
  exact leviC_add
    (((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).of_le (by norm_num))
    (((hg x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).of_le (by norm_num))

theorem levi_const_mul (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    levi (fun y => c * f y) x = (c : ℂ) • levi f x := by
  exact leviC_const_mul
    (((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))).of_le (by norm_num)) c

theorem laplacian_add (k : HermitianField M) (f g : M.Carrier → ℝ)
    (hf : SmoothFn f) (hg : SmoothFn g) (x : M.Carrier) :
    laplacian k (fun y => f y + g y) x = laplacian k f x + laplacian k g x := by
  simp only [laplacian, levi_add f g hf hg, traceWith, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re]

theorem laplacian_const_mul (k : HermitianField M) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (c : ℝ) (x : M.Carrier) :
    laplacian k (fun y => c * f y) x = c * laplacian k f x := by
  simp only [laplacian, levi_const_mul f hf c, traceWith, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

end Yau.Proofs.C05Aux
