import Yau.Proofs.F01ScalarLeviDiagonal
import Yau.Proofs.F01DiagonalCovectorNorm
import Yau.Proofs.F01ConformalGradient

/-! The actual trace of the logarithmic complex Hessian in the positive
diagonal frame, retaining the exact native inverse-transpose gradient norm. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem traceWith_real_diagonal (values : Fin n → ℝ) (hv : ∀ i, values i ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ))) A =
      ∑ i, (values i)⁻¹ * (A i i).re := by
  unfold traceWith
  rw [inverse_real_diagonal values hv]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem traceWith_leviC_log_real_diagonal (values : Fin n → ℝ)
    (hv : ∀ i, values i ≠ 0) {q : ComplexVector n → ℝ} {z : ComplexVector n}
    (hq : ContDiffAt ℝ 2 q z) (hpos : 0 < q z) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ)))
        (leviC (fun w => Real.log (q w)) z) =
      (q z)⁻¹ * traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC q z) -
        dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
          (WithLp.toLp 2 (fun i => wirt (fun w => (Real.log (q w) : ℂ)) z (stdVec i))) := by
  have hlog (i : Fin n) : wirt (fun w => (Real.log (q w) : ℂ)) z (stdVec i) =
      (((q z)⁻¹ : ℝ) : ℂ) * wirt (fun w => (q w : ℂ)) z (stdVec i) :=
    wirt_ofReal_scalar_comp (hq.differentiableAt (by norm_num))
      (Real.hasDerivAt_log hpos.ne') (stdVec i)
  rw [traceWith_real_diagonal values hv, traceWith_real_diagonal values hv,
    dualNormMat_real_diagonal values hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [leviC_log_diagonal hq hpos, hlog, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  ring

end Yau.NodeProofs.F01Aux
