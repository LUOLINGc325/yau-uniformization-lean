import Yau.Proofs.V03QuadraticWithinDerivative

/-! The native real within derivative of a complex coefficient is exactly
the complex combination of its actual real and imaginary scalar derivatives. -/

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem fderivWithin_complex_eq_re_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {x : E} (hS : UniqueDiffWithinAt ℝ S x) {f : E → ℂ}
    (hf : DifferentiableWithinAt ℝ f S x) (v : E) :
    fderivWithin ℝ f S x v =
      (fderivWithin ℝ (fun y => (f y).re) S x v : ℂ) +
        Complex.I * (fderivWithin ℝ (fun y => (f y).im) S x v : ℂ) := by
  have hRe : fderivWithin ℝ (fun y => (f y).re) S x v = (fderivWithin ℝ f S x v).re := by
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A v)
      ((Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hS)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, Complex.reCLM_apply] using hh
  have hIm : fderivWithin ℝ (fun y => (f y).im) S x v = (fderivWithin ℝ f S x v).im := by
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A v)
      ((Complex.imCLM.hasFDerivAt.comp_hasFDerivWithinAt x hf.hasFDerivWithinAt).fderivWithin hS)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, Complex.imCLM_apply] using hh
  rw [hRe, hIm]
  calc
    _ = ((fderivWithin ℝ f S x v).re : ℂ) + ((fderivWithin ℝ f S x v).im : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm
    _ = _ := by ring

end Yau.Blueprint.V03Proof
