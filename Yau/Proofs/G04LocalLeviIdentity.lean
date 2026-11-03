import Yau.Proofs.G04SignedFormInverse
import Yau.LeafProofs.L22LeviBasic

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def jScalarComponents (q : ComplexVector n → ℝ) : FormComponents n 1 :=
  fun z I => L12Aux.jSign (I 0) * rDeriv q z (L12Aux.jIndex n (I 0))

theorem exterior_jScalarComponents {q : ComplexVector n → ℝ} {z : ComplexVector n}
    (hq : ContDiffAt ℝ 2 q z) (I : Fin 2 → RIdx n) :
    exteriorComponents (jScalarComponents q) z I =
      L12Aux.jSign (I 1) * fderiv ℝ (fderiv ℝ q) z (realVec (I 0)) (realVec (L12Aux.jIndex n (I 1))) -
      L12Aux.jSign (I 0) * fderiv ℝ (fderiv ℝ q) z (realVec (I 1)) (realVec (L12Aux.jIndex n (I 0))) := by
  have hdf (b : RIdx n) : DifferentiableAt ℝ (fun w => rDeriv q w b) z :=
    ((hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const (realVec b))
  unfold exteriorComponents
  simp [Fin.sum_univ_succ, Fin.succAbove, jScalarComponents]
  rw [L12Aux.rDeriv_const_mul (hdf _) _ _, L12Aux.rDeriv_const_mul (hdf _) _ _,
    L12Aux.rDeriv_rDeriv_eq_hessian hq, L12Aux.rDeriv_rDeriv_eq_hessian hq]
  ring

theorem local_dd_levi {q : ComplexVector n → ℝ} {z : ComplexVector n}
    (hq : ContDiffAt ℝ 2 q z) (I : Fin 2 → RIdx n) :
    -(1 / 2 : ℝ) * exteriorComponents (jScalarComponents q) z I =
      2 * (matrixPairing (leviC q z) (realVec (I 0)) (realVec (I 1))).im := by
  rw [exterior_jScalarComponents hq]
  rcases h0 : I 0 with ⟨a, ar⟩
  rcases h1 : I 1 with ⟨b, br⟩
  have hre := (L18Aux.leviMatrix_entry_re_im hq stdVec a b).1
  have him := (L18Aux.leviMatrix_entry_re_im hq stdVec a b).2
  have hsymm := hq.isSymmSndFDerivAt (by norm_num)
  have h00 := hsymm (stdVec a) (stdVec b)
  have h01 := hsymm (stdVec a) (Complex.I • stdVec b)
  have h10 := hsymm (Complex.I • stdVec a) (stdVec b)
  have h11 := hsymm (Complex.I • stdVec a) (Complex.I • stdVec b)
  fin_cases ar <;> fin_cases br <;>
    simp [L12Aux.jIndex, L12Aux.jSign, realVec, matrixPairing,
      EuclideanSpace.single, apply_ite, leviC, hre, him, Complex.mul_re, Complex.mul_im] <;>
    simp only [stdVec, EuclideanSpace.single] at h00 h01 h10 h11 ⊢ <;> linarith

end Yau.NodeProofs.G04Aux
