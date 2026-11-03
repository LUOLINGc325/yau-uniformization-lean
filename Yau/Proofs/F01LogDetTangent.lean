import Yau.Proofs.F01SimultaneousHermitian
import Yau.Proofs.F01TraceOrder
import Yau.Proofs.F01LogDetOrder

/-! The genuine logarithmic determinant lies below its actual tangent
trace. This gives the scalar comparison for two actual potential flows. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem matrix_logdet_le_tangent_trace
    {H K : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) (hK : K.PosDef) :
    Real.log (K.det.re / H.det.re) ≤ traceWith H (K - H) := by
  obtain ⟨J, hJ, hnormal, values, hdiag⟩ :=
    simultaneous_hermitian_normalization H K hH hK.isHermitian
  have hJdet : J.det ≠ 0 := (hJ.map Matrix.detMonoidHom).ne_zero
  have hdiagpos : (Matrix.diagonal (fun i => (values i : ℂ))).PosDef := by
    rw [← hdiag]
    exact hK.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hJ)
  have hvpos (i : Fin n) : 0 < values i :=
    Complex.zero_lt_real.mp ((Matrix.posDef_diagonal_iff.mp hdiagpos) i)
  have hratio := determinant_ratio_congruence K H J hJdet
  rw [hdiag, hnormal, Matrix.det_one, Complex.one_re, div_one, Matrix.det_diagonal] at hratio
  have hprodComplex : (∏ i, (values i : ℂ)) = ((∏ i, values i : ℝ) : ℂ) := by norm_cast
  rw [hprodComplex, Complex.ofReal_re] at hratio
  have hlog : Real.log (K.det.re / H.det.re) = ∑ i, Real.log (values i) := by
    rw [← hratio, Real.log_prod (fun i _ => (hvpos i).ne')]
  have htrace : traceWith H (K - H) = ∑ i, (values i - 1) := by
    rw [← traceWith_congruence H (K - H) J hJdet]
    simp only [Matrix.mul_sub, Matrix.sub_mul, hdiag, hnormal, traceWith,
      inv_one, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_diagonal,
      Matrix.trace_one, Complex.sub_re, Complex.re_sum, Complex.ofReal_re]
    simp [Finset.sum_sub_distrib]
  rw [hlog, htrace]
  exact Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hvpos i))

end Yau.NodeProofs.F01Aux
