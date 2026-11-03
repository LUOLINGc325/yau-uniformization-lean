import Yau.LeafProofs.L17RicciNaturality

/-! Actual scalar Hessian subtraction and the linear native matrix trace. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem leviC_sub {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun w => f w - g w) z = leviC f z - leviC g z := by
  have hh := leviC_add hf ((contDiffAt_const (c := (-1 : ℝ))).mul hg)
  rw [leviC_const_mul hg (-1)] at hh
  simpa only [neg_one_mul, Complex.ofReal_neg, Complex.ofReal_one,
    neg_smul, one_smul, sub_eq_add_neg] using hh

theorem traceWith_add (H A B : Matrix (Fin n) (Fin n) ℂ) :
    traceWith H (A + B) = traceWith H A + traceWith H B := by
  simp only [traceWith, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

theorem traceWith_sub (H A B : Matrix (Fin n) (Fin n) ℂ) :
    traceWith H (A - B) = traceWith H A - traceWith H B := by
  simp only [traceWith, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

end Yau.NodeProofs.F01Aux
