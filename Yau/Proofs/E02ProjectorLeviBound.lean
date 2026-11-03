import Yau.Proofs.E02GrassmannTraceBound
import Yau.Proofs.E02RectangularLevi

open Matrix
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The constant-one bound applies to the literal projector penalty's
calculated Levi, with every ordinary derivative already proved. -/
theorem projectorPenalty_rectLevi_le_logGram {n m : ℕ} (M₀ M Z : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) :
    rectLevi (projectorPenalty (n := n) (rowProjector M₀)) M Z ≤ rectLevi logGram M Z := by
  rw [projectorPenalty_rectLevi_computed (rowProjector M₀) M Z hM,
    logGram_rectLevi_eq M Z hM]
  simp only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]
  exact projector_trace_bound M₀ hM₀ (projectorTangent M Z)

theorem logGram_sub_penalty_rectLevi_lower {n m : ℕ} (M₀ M Z : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) {θ : ℝ} (hθ : 0 ≤ θ) :
    (1-θ)*rectLevi logGram M Z ≤ rectLevi logGram M Z-
      θ*rectLevi (projectorPenalty (n := n) (rowProjector M₀)) M Z := by
  have h := mul_le_mul_of_nonneg_left (projectorPenalty_rectLevi_le_logGram M₀ M Z hM₀ hM) hθ
  nlinarith

theorem logGram_sub_penalty_rectLevi_nonneg {n m : ℕ} (M₀ M Z : Rect n m)
    (hM₀ : (M₀*M₀ᴴ).PosDef) (hM : (M*Mᴴ).PosDef) {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    0 ≤ rectLevi logGram M Z-θ*rectLevi (projectorPenalty (n := n) (rowProjector M₀)) M Z :=
  (mul_nonneg (sub_nonneg.mpr hθ₁) (logGram_rectLevi_nonneg M Z hM)).trans
    (logGram_sub_penalty_rectLevi_lower M₀ M Z hM₀ hM hθ₀)

end Yau.NodeProofs.E02Aux
