import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! First variation of the actual complex determinant along real matrix lines. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint Polynomial

variable {n : ℕ}

theorem determinant_one_line_hasDerivAt_complex (M : Herm n) :
    HasDerivAt (fun z : ℂ => (1 + z • M).det) (Matrix.trace M) 0 := by
  let p : Polynomial ℂ := Matrix.det
    ((1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)
  have heval (z : ℂ) : p.eval z = (1 + z • M).det := by
    change (Polynomial.evalRingHom z) _ = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_comm (M i j) z]
    congr 1
    by_cases hij : i = j <;>
      simp only [Matrix.one_apply, hij, ite_true, ite_false,
        Polynomial.eval_one, Polynomial.eval_zero]
  have hd : p.derivative.eval 0 = Matrix.trace M :=
    Matrix.derivative_det_one_add_X_smul M
  simpa only [heval, hd] using p.hasDerivAt (0 : ℂ)

theorem determinant_one_line_hasDerivAt (M : Herm n) :
    HasDerivAt (fun s : ℝ => (1 + (s : ℂ) • M).det.re)
      (Matrix.trace M).re 0 :=
  (determinant_one_line_hasDerivAt_complex M).real_of_complex

theorem determinant_line_hasDerivAt_complex (A H : Herm n) (hA : IsUnit A) :
    HasDerivAt (fun z : ℂ => (A + z • H).det)
      (A.det * Matrix.trace (A⁻¹ * H)) 0 := by
  have heq : (fun z : ℂ => (A + z • H).det) =
      (fun z => A.det * (1 + z • (A⁻¹ * H)).det) := by
    funext z
    rw [← Matrix.det_mul]
    congr 1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv A (hA.map Matrix.detMonoidHom), Matrix.one_mul]
  rw [heq]
  exact (determinant_one_line_hasDerivAt_complex (A⁻¹ * H)).const_mul A.det

theorem determinant_line_hasDerivAt (A H : Herm n) (hA : A.PosDef) :
    HasDerivAt (fun s : ℝ => (A + (s : ℂ) • H).det.re)
      (A.det.re * (Matrix.trace (A⁻¹ * H)).re) 0 := by
  have him : A.det.im = 0 := (Complex.pos_iff.mp hA.det_pos).2.symm
  simpa only [Complex.mul_re, him, zero_mul, sub_zero] using
    (determinant_line_hasDerivAt_complex A H hA.isUnit).real_of_complex

end Yau.NodeProofs.E01Aux
