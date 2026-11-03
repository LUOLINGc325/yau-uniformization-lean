import Yau.Proofs.V03CovectorTransport

/-! Native normalization of the real differential of a real scalar and
complex linearity of the actual cotangent coordinate identification. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem real_fderiv_eq_two_re_wirt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z) (v : E) :
    fderiv ℝ f z v = 2 * (wirt (fun y => (f y : ℂ)) z v).re := by
  simp only [wirt, fderiv_ofReal_apply hf, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero]
  norm_num
  ring

theorem cotangentVectorOfCoords_smul {n : ℕ} (c : ℂ) (v : CotangentIndex n → ℂ) :
    cotangentVectorOfCoords (c • v) = c • cotangentVectorOfCoords v := by
  ext i <;> rfl

end Yau.Blueprint.V03Proof
