import Yau.Proofs.F01NormalizeHermitian
import Yau.Proofs.F01PenalizedHeatChain
import Yau.LeafProofs.L17ScalarChartOperator

/-! Positivity and monotonicity of the actual inverse-metric trace,
proved by an actual invertible normalization of its positive metric. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ}

theorem traceWith_posSemidef_nonneg {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hA : A.PosSemidef) : 0 ≤ traceWith H A := by
  obtain ⟨J, hJ, hnormal⟩ := positive_hermitian_normalization H hH
  have hdet : J.det ≠ 0 := (hJ.map Matrix.detMonoidHom).ne_zero
  rw [← traceWith_congruence H A J hdet, hnormal]
  have hpos := (Complex.nonneg_iff.mp (hA.conjTranspose_mul_mul_same J).trace_nonneg).1
  simpa only [traceWith, inv_one, Matrix.one_mul] using hpos

theorem traceWith_mono {H A B : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hAB : (B - A).PosSemidef) : traceWith H A ≤ traceWith H B := by
  have hh := traceWith_posSemidef_nonneg hH hAB
  rw [traceWith_sub] at hh
  exact sub_nonneg.mp hh

theorem traceWith_lower_scalar {H A B : Matrix (Fin n) (Fin n) ℂ} {c : ℝ}
    (hH : H.PosDef) (hAB : (A - (c : ℂ) • B).PosSemidef) :
    c * traceWith H B ≤ traceWith H A := by
  have hh := traceWith_posSemidef_nonneg hH hAB
  rw [traceWith_sub, traceWith_real_smul] at hh
  exact sub_nonneg.mp hh

end Yau.NodeProofs.F01Aux
