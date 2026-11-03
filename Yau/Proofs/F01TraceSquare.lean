import Yau.Proofs.F01TraceOrder

/-! The exact inverse-metric square in the scalar evolution is
nonnegative for the actual Hermitian Ricci matrix. -/
noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem inverse_metric_trace_square_nonneg {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hA : A.IsHermitian) :
    0 ≤ (Matrix.trace (H⁻¹ * A * H⁻¹ * A)).re := by
  have hpos := hH.inv.posSemidef.conjTranspose_mul_mul_same A
  change Aᴴ = A at hA
  rw [hA] at hpos
  have htrace := traceWith_posSemidef_nonneg hH hpos
  simpa only [traceWith, Matrix.mul_assoc] using htrace

end Yau.NodeProofs.F01Aux
