import Yau.Proofs.F01LogDetMixed
import Yau.Proofs.F01DiagonalSquareTrace
import Yau.Proofs.F01HermitianMatrixJets
import Yau.Proofs.F01DiagonalRayleigh

/-! The actual diagonal log-determinant Hessian has the full negative
weighted squared first-jet term, with positivity derived from the metric. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem logdet_diagonal_levi_formula
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ) {S : Set (ComplexVector n)}
    (hS : IsOpen S) (hH : ∀ i j, ContDiffOn ℝ ∞ (fun w => H w i j) S)
    (hpos : ∀ w ∈ S, (H w).PosDef) {z : ComplexVector n} (hz : z ∈ S)
    (values : Fin n → ℝ) (hdiag : H z = Matrix.diagonal (fun i => (values i : ℂ))) (a : Fin n) :
    (leviC (fun w => Real.log (H w).det.re) z a a).re =
      (∑ i, (values i)⁻¹ *
        (wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a)).re) -
      ∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
        Complex.normSq (wirt (fun w => H w j i) z (stdVec a)) := by
  have hvalues (i : Fin n) : 0 < values i := by
    have hsingle : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have hh := congrFun h i
      simpa using hh
    have hp := matrixQuadraticValue_pos (hpos z hz) hsingle
    simpa only [matrixQuadraticValue_single, hdiag, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] using hp
  have hInv : (H z)⁻¹ = Matrix.diagonal (fun i => (((values i)⁻¹ : ℝ) : ℂ)) := by
    rw [hdiag]
    exact inverse_real_diagonal values (fun i => (hvalues i).ne')
  have hBdiag (i : Fin n) :
      matrixBarJet (fun y => matrixUnbarJet H y (stdVec a)) z (stdVec a) i i =
        wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a) := by
    exact (L14Aux.wirt_wirtBar_comm (fun y => H y i i) z
      (((hH i i).contDiffAt (hS.mem_nhds hz)).of_le (by simp)) (stdVec a) (stdVec a)).symm
  have ht : (Matrix.trace ((H z)⁻¹ *
      matrixBarJet (fun y => matrixUnbarJet H y (stdVec a)) z (stdVec a))).re =
        ∑ i, (values i)⁻¹ *
          (wirt (fun w => wirtBar (fun y => H y i i) w (stdVec a)) z (stdVec a)).re := by
    rw [hInv]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simp_rw [hBdiag]
  have hq : (Matrix.trace ((H z)⁻¹ * matrixBarJet H z (stdVec a) * (H z)⁻¹ *
      matrixUnbarJet H z (stdVec a))).re =
        ∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
          Complex.normSq (matrixUnbarJet H z (stdVec a) j i) := by
    rw [hInv, matrixBarJet_eq_conjTranspose_unbar H hS (fun w hw => (hpos w hw).isHermitian) hz]
    exact weighted_square_trace (fun i => (values i)⁻¹) (matrixUnbarJet H z (stdVec a))
  have hr := congrArg Complex.re (logdet_mixed_inverse_trace H hS hH hpos hz (stdVec a) (stdVec a))
  rw [Matrix.trace_sub, Complex.sub_re, ht, hq] at hr
  exact hr

end Yau.NodeProofs.F01Aux
