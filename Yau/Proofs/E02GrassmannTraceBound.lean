import Yau.Proofs.E02MatrixBasic
import Yau.Proofs.V05Matrix

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The algebraic trace estimate used only AFTER the actual projector
Levi identity has been calculated. It does not define that Levi identity. -/
theorem projector_trace_bound {n m : ℕ} (M₀ : Rect n m) (hM₀ : (M₀*M₀ᴴ).PosDef)
    (S : Herm m) :
    (Matrix.trace (rowProjector M₀*(S*Sᴴ))).re-
      (Matrix.trace (rowProjector M₀*(Sᴴ*S))).re ≤ (Matrix.trace (S*Sᴴ)).re := by
  have hP := rowProjector_posSemidef M₀ hM₀
  have hQ := one_sub_rowProjector_posSemidef M₀ hM₀
  have h1 := V05Aux.trace_mul_nonneg hP (Matrix.posSemidef_conjTranspose_mul_self S)
  have h2 := V05Aux.trace_mul_nonneg hQ (Matrix.posSemidef_self_mul_conjTranspose S)
  have h1r := (RCLike.nonneg_iff.mp h1).1
  have h2r := (RCLike.nonneg_iff.mp h2).1
  change 0 ≤ (Matrix.trace (rowProjector M₀*(Sᴴ*S))).re at h1r
  change 0 ≤ (Matrix.trace ((1-rowProjector M₀)*(S*Sᴴ))).re at h2r
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re] at h2r
  linarith

end Yau.NodeProofs.E02Aux
