import Yau.Proofs.P03LogHessian
import Yau.Proofs.P03PoleRegularization
import Yau.LeafProofs.L22LeviBasic

open scoped Topology ContDiff InnerProductSpace

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem regularizedNormSq_hasFDerivAt (a : ComplexVector n) (ε : ℝ) (z : ComplexVector n) :
    HasFDerivAt (fun w : ComplexVector n => ‖w - a‖ ^ 2 + ε)
      (2 • innerSL ℝ (z - a)) z := by
  convert! (((hasFDerivAt_id z).sub_const a).norm_sq.add_const ε) using 1

theorem regularizedNormSq_secondFDeriv (a : ComplexVector n) (ε : ℝ)
    (z v w : ComplexVector n) :
    fderiv ℝ (fderiv ℝ (fun y : ComplexVector n => ‖y - a‖ ^ 2 + ε)) z v w =
      2 * inner ℝ v w := by
  have he : fderiv ℝ (fun y : ComplexVector n => ‖y - a‖ ^ 2 + ε) =
      fun y => 2 • innerSL ℝ (y - a) := by
    funext y
    exact (regularizedNormSq_hasFDerivAt a ε y).fderiv
  rw [he]
  have hd := ((2 • innerSL ℝ (E := ComplexVector n)).hasFDerivAt).comp z
    ((hasFDerivAt_id z).sub_const a)
  have hde := congrArg (fun L : ComplexVector n →L[ℝ] (ComplexVector n →L[ℝ] ℝ) => L v w)
    hd.fderiv
  convert! hde using 1 <;>
    simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_apply, two_smul, ContinuousLinearMap.add_apply, innerSL_apply_apply] <;> ring <;> rfl

/-- Exact real line-Hessian formula for the regularized logarithmic pole. -/
theorem modelLogPole_complexLevi (a z v : ComplexVector n) {ε : ℝ} (hε : 0 < ε) :
    complexLeviQuadratic (modelLogPole a ε) z v =
      ‖v‖ ^ 2 / (‖z - a‖ ^ 2 + ε) -
        ((inner ℝ (z - a) v) ^ 2 + (inner ℝ (z - a) (Complex.I • v)) ^ 2) /
          (‖z - a‖ ^ 2 + ε) ^ 2 := by
  let q := fun w : ComplexVector n => ‖w - a‖ ^ 2 + ε
  have hq : ContDiff ℝ ∞ q :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const
  have hn : q z ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)
  have hd (w : ComplexVector n) : fderiv ℝ q z w = 2 * inner ℝ (z - a) w := by
    convert! congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L w)
      (regularizedNormSq_hasFDerivAt a ε z).fderiv using 1 <;>
      simp only [q, smul_apply, two_smul, ContinuousLinearMap.add_apply, innerSL_apply_apply] <;> ring <;> rfl
  change (fderiv ℝ (fderiv ℝ (fun w => Real.log (q w))) z v v +
    fderiv ℝ (fderiv ℝ (fun w => Real.log (q w))) z (Complex.I • v) (Complex.I • v)) / 4 = _
  rw [secondFDeriv_log q hq z v v hn,
    secondFDeriv_log q hq z (Complex.I • v) (Complex.I • v) hn,
    regularizedNormSq_secondFDeriv a ε z v v,
    regularizedNormSq_secondFDeriv a ε z (Complex.I • v) (Complex.I • v), hd, hd]
  simp only [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  simp only [q, div_eq_mul_inv]
  ring

end Yau.NodeProofs.P03Aux
