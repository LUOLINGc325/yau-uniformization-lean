import Yau.LeafProofs.L07

/-! The first real derivative of the actual positive Hermitian determinant
logarithm is the original complex inverse-matrix trace. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem logdet_fderiv_trace (H : E → Matrix (Fin n) (Fin n) ℂ) (z v : E)
    (hH : DifferentiableAt ℝ H z) (hpos : (H z).PosDef) :
    fderiv ℝ (fun w => Real.log (H w).det.re) z v =
      traceWith (H z) (fderiv ℝ H z v) := by
  have hd := L07Aux.matrix_determinant_differentiableAt H z hH
  have hreal : HasFDerivAt (fun w => (H w).det.re)
      (Complex.reCLM.comp (fderiv ℝ (fun w => (H w).det) z)) z :=
    Complex.reCLM.hasFDerivAt.comp z hd.hasFDerivAt
  have hp := Complex.pos_iff.mp hpos.det_pos
  have him : (H z).det.im = 0 := hp.2.symm
  have heq : fderiv ℝ (fun w => Real.log (H w).det.re) z v =
      (H z).det.re⁻¹ * (fderiv ℝ (fun w => (H w).det) z v).re := by
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) (hreal.log hp.1.ne').fderiv
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      Complex.reCLM_apply, smul_eq_mul] using hh
  rw [heq, L07Aux.determinant_fderiv_trace H z v hH
    (hpos.isUnit.map Matrix.detMonoidHom)]
  simp only [Complex.mul_re, him, zero_mul, sub_zero, traceWith]
  rw [← mul_assoc, inv_mul_cancel₀ hp.1.ne', one_mul]

end Yau.NodeProofs.F01Aux
