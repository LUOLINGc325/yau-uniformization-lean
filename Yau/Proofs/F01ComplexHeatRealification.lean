import Yau.Proofs.F01RealHessianLeviLinear

/-! The native inverse complex trace is the actual real nondivergence
operator with coefficient one quarter of the raw inverse realification.
The factor is computed from the nested Wirtinger derivatives. -/
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def complexHeatCoefficient (H : Matrix (Fin n) (Fin n) ℂ) : Mat n :=
  (1 / 4 : ℝ) • G01Aux.rawReal H⁻¹

theorem traceWith_leviC_eq_real_contraction
    (H : Matrix (Fin n) (Fin n) ℂ) {q : Space n → ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q z) :
    traceWith H (leviC q z) =
      ∑ a : RIdx n, ∑ b : RIdx n, complexHeatCoefficient H a b *
        fderiv ℝ (fderiv ℝ q) z (realVec a) (realVec b) := by
  simp only [traceWith, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, Complex.mul_re]
  conv_rhs => simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hre := (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hq stdVec j i).1
  have him := (Yau.LeafProofs.L18Aux.leviMatrix_entry_re_im hq stdVec j i).2
  simp only [leviC, hre, him]
  simp [complexHeatCoefficient, G01Aux.rawReal, realVec, stdVec, Matrix.smul_apply]
  ring

theorem native_complex_heat_eq_real_operator
    {u : Point n → ℝ} {Q : Set (Point n)} {p : Point n}
    (H : Matrix (Fin n) (Fin n) ℂ)
    (hu : ContDiffAt ℝ 2 (fun z => u (z, p.2)) p.1) :
    linearOp Q (fun _ => complexHeatCoefficient H) (fun _ _ => 0) u p =
      timeD Q u p - traceWith H (leviC (fun z => u (z, p.2)) p.1) := by
  rw [traceWith_leviC_eq_real_contraction H hu]
  simp only [linearOp, spatialDD, zero_mul, Finset.sum_const_zero, sub_zero]

end Yau.NodeProofs.F01Aux
