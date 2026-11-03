import Yau.Proofs.E02LogdetSupport
import Yau.Proofs.E02ProjectionPenalty

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

def matrixSupportGap {n m : ℕ} (W lam θ : ℝ) (M₀ M : Rect n m) : ℝ :=
  W-((n:ℝ)+lam+Real.log (M*Mᴴ).det.re-θ*projectorPenalty (rowProjector M₀) M)

/-- The four genuine pointwise support errors are nonnegative. Vanishing
forces the full Gram/projector equality orbit, with no isolated contact. -/
theorem matrixSupportGap_nonneg_eq {n m : ℕ} (B : Herm n) (hB : B.PosDef)
    (M₀ M : Rect n m) (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef)
    (W lam θ : ℝ) (hθ : 0 < θ) (hLam : lam ≤ Real.log B.det.re)
    (hW : (Matrix.trace (B*(M*Mᴴ))).re ≤ W) :
    0 ≤ matrixSupportGap W lam θ M₀ M ∧
      (matrixSupportGap W lam θ M₀ M = 0 →
        lam = Real.log B.det.re ∧ M*Mᴴ = B⁻¹ ∧
        rowProjector M = rowProjector M₀ ∧ W = (Matrix.trace (B*(M*Mᴴ))).re) := by
  have hSupport := trace_logdet_support (M*Mᴴ) B hM hB
  have hPen := projectorPenalty_nonneg_eq_zero M₀ M hM₀ hM
  have hθPen : 0 ≤ θ*projectorPenalty (rowProjector M₀) M := mul_nonneg hθ.le hPen.1
  constructor
  · unfold matrixSupportGap
    linarith
  · intro hZero
    unfold matrixSupportGap at hZero
    have hLamEq : lam = Real.log B.det.re := by linarith
    have hθPenZero : θ*projectorPenalty (rowProjector M₀) M = 0 := by linarith
    have hPenZero : projectorPenalty (rowProjector M₀) M = 0 :=
      (mul_eq_zero.mp hθPenZero).resolve_left hθ.ne'
    have hEq : (n:ℝ)+Real.log (M*Mᴴ).det.re+Real.log B.det.re =
        (Matrix.trace (B*(M*Mᴴ))).re := by linarith
    have hGram := (trace_logdet_support_eq_iff (M*Mᴴ) B hM hB).mp hEq
    exact ⟨hLamEq,hGram,hPen.2.mp hPenZero,by linarith⟩

end Yau.NodeProofs.E02Aux
