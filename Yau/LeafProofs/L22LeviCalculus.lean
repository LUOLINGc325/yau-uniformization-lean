import Yau.LeafProofs.L22LeviBasic

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Filter

namespace Yau.LeafProofs.L22Aux

theorem secondFDeriv_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => f x + g x)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w + fderiv ℝ (fderiv ℝ g) z v w := by
  have hh := congrArg (fun A => A ![v,w]) (iteratedFDeriv_add_apply hf hg)
  simpa only [Pi.add_def, iteratedFDeriv_two_apply, add_apply,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

theorem secondFDeriv_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun x => c * f x)) z v w =
      c * fderiv ℝ (fderiv ℝ f) z v w := by
  have hh := congrArg (fun A => A ![v,w]) (iteratedFDeriv_const_smul_apply (a := c) hf)
  simpa only [Pi.smul_def, iteratedFDeriv_two_apply, smul_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

theorem complexLeviQuadratic_add {n : ℕ} {f g : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v : ComplexVector n) :
    complexLeviQuadratic (fun x => f x + g x) z v =
      complexLeviQuadratic f z v + complexLeviQuadratic g z v := by
  simp only [complexLeviQuadratic, secondFDeriv_add hf hg]
  ring

theorem complexLeviQuadratic_const_mul {n : ℕ} {f : ComplexVector n → ℝ}
    {z : ComplexVector n} (hf : ContDiffAt ℝ 2 f z) (c : ℝ) (v : ComplexVector n) :
    complexLeviQuadratic (fun x => c * f x) z v = c * complexLeviQuadratic f z v := by
  simp only [complexLeviQuadratic, secondFDeriv_const_mul hf]
  ring

theorem complexLeviQuadratic_zero {n : ℕ} (z v : ComplexVector n) :
    complexLeviQuadratic (fun _ => (0 : ℝ)) z v = 0 := by
  simp [complexLeviQuadratic]

theorem complexLeviQuadratic_smul {n : ℕ} (f : ComplexVector n → ℝ)
    (z v : ComplexVector n) (c : ℝ) :
    complexLeviQuadratic f z (c • v) = c ^ 2 * complexLeviQuadratic f z v := by
  simp only [complexLeviQuadratic, smul_comm Complex.I c, map_smul,
    smul_apply, smul_eq_mul]
  ring

/-- A holomorphic pullback has the line-Hessian of the complex differential. -/
theorem complexLeviQuadratic_comp {n m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (v : ComplexVector n) :
    complexLeviQuadratic (f ∘ T) z v =
      complexLeviQuadratic f (T z) (fderiv ℂ T z v) := by
  have hd := hT.differentiableAt (by norm_num)
  have hreal (w : ComplexVector n) : fderiv ℝ T z w = fderiv ℂ T z w := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector m => L w)
      (hd.fderiv_restrictScalars ℝ)
  simp only [complexLeviQuadratic, L18Aux.secondFDeriv_comp (hT.restrict_scalars ℝ) hf,
    L18Aux.secondFDeriv_complex_I_I hT, map_neg, hreal, map_smul]
  ring

end Yau.LeafProofs.L22Aux
