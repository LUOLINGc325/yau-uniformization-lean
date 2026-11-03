import Yau.Proofs.F01WirtingerLinear
import Yau.Proofs.F01CovectorCauchy

/-! The original Wirtinger differential controls the real line derivatives
with the exact quarter normalization. -/
noncomputable section
open scoped ComplexOrder Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem norm_wirt_ofReal_sq {u : ComplexVector n → ℝ} {z : ComplexVector n}
    (hu : DifferentiableAt ℝ u z) (v : ComplexVector n) :
    ‖wirt (fun w => (u w : ℂ)) z v‖ ^ 2 =
      ((fderiv ℝ u z v) ^ 2 + (fderiv ℝ u z (Complex.I • v)) ^ 2) / 4 := by
  have hd : fderiv ℝ (fun w => (u w : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ u z) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ u) z = _
    rw [fderiv_comp z Complex.ofRealCLM.differentiableAt hu]
    simp
  simp only [wirt, hd, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub]
  norm_num
  ring

theorem gradient_quadratic_cauchy (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {u : ComplexVector n → ℝ} {z : ComplexVector n}
    (hu : DifferentiableAt ℝ u z) (v : ComplexVector n) :
    ((fderiv ℝ u z v) ^ 2 + (fderiv ℝ u z (Complex.I • v)) ^ 2) / 4 ≤
      dualNormMat H (WithLp.toLp 2 (fun i => wirt (fun w => (u w : ℂ)) z (stdVec i))) *
        (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re := by
  rw [← norm_wirt_ofReal_sq hu, wirt_eq_coordinate_contraction]
  have hc := matrix_covector_cauchy H hH
    (fun i : Fin n => wirt (fun w => (u w : ℂ)) z (stdVec i)) (WithLp.ofLp v)
  simpa only [Complex.sq_norm, dualNormMat, WithLp.ofLp_toLp] using hc

end Yau.NodeProofs.F01Aux
