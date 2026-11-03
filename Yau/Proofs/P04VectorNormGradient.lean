import Yau.Proofs.P04SquaredNormHessian

noncomputable section
open scoped Topology ContDiff InnerProductSpace

namespace Yau.Proofs.P04Aux
open Yau

/-- The actual vector-valued holomorphic norm differential, at every value. -/
theorem wirt_vectorNormSq_holomorphic {n m : ℕ}
    {f : ComplexVector n → ComplexVector m} {z : ComplexVector n}
    (hf : DifferentiableAt ℂ f z) (v : ComplexVector n) :
    wirt (fun y => ((‖f y‖^2 : ℝ) : ℂ)) z v = ⟪f z,fderiv ℂ f z v⟫_ℂ := by
  have hR := hf.hasFDerivAt.restrictScalars ℝ
  have hN := hR.norm_sq
  have hD (w : ComplexVector n) : fderiv ℝ (fun y => ‖f y‖^2) z w =
      2*(⟪f z,fderiv ℂ f z w⟫_ℂ).re := by
    rw [hN.fderiv]
    simp only [smul_apply,ContinuousLinearMap.comp_apply,innerSL_apply_apply,two_smul]
    change ⟪f z,fderiv ℂ f z w⟫_ℝ+⟪f z,fderiv ℂ f z w⟫_ℝ = _
    rw [model_real_inner]
    ring
  rw [wirt_ofReal_formula hN.differentiableAt,hD,hD,map_smul,inner_smul_right]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

end Yau.Proofs.P04Aux
