import Yau.Proofs.P06OrderAlgebra

noncomputable section
open scoped ComplexOrder MatrixOrder

namespace Yau.NodeProofs.P06Aux.Clip
open Yau.NodeProofs.P06Aux

def matrixPositivePart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A⁺

theorem matrixPositivePart_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixPositivePart A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)

/-- The true matrix positive part satisfies the Hilbert–Schmidt normal
inequality for every positive Hermitian competitor. Positivity follows
from the finite matrix order; no heat or form-domain property is assumed. -/
theorem matrixPositivePart_normal {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef) :
    (Matrix.trace ((A - matrixPositivePart A) * (B - matrixPositivePart A))).re ≤ 0 := by
  have hN : (A⁻).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have htr := matrix_trace_mul_nonneg A⁻ B hN hB
  have hd : A - A⁺ = -A⁻ := by
    have he := CFC.posPart_sub_negPart A (show IsSelfAdjoint A from hA)
    calc
      A - A⁺ = (A⁺ - A⁻) - A⁺ := by rw [he]
      _ = -A⁻ := by abel
  change (Matrix.trace ((A - A⁺) * (B - A⁺))).re ≤ 0
  rw [hd, neg_mul, Matrix.mul_sub, CFC.negPart_mul_posPart, sub_zero,
    Matrix.trace_neg, Complex.neg_re]
  exact neg_nonpos.mpr htr

end Yau.NodeProofs.P06Aux.Clip
