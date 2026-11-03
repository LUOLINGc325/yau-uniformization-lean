import Yau.Proofs.D02LoweringSecondDerivative

/-! The dual Bochner identity follows by differentiating the proved lowering
identity. Its curvature matrix is computed, with no positivity input for it. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs.L14Aux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {r : ℕ}

theorem dualBochner_identity {U : Set V} (hU : IsOpen U)
    (D : V → Matrix (Fin r) (Fin r) ℂ) (t η : V → Fin r → ℂ)
    (hD : ∀ a b, ContDiffOn ℝ ∞ (fun w => D w a b) U)
    (ht : ∀ a, ContDiffOn ℝ ∞ (fun w => t w a) U)
    (hη : ∀ a, DifferentiableOn ℂ (fun w => η w a) U)
    (hPos : ∀ w ∈ U, (D w).PosDef)
    (hLower : ∀ w ∈ U, D w *ᵥ t w = η w) (z v : V) (hz : z ∈ U) :
    wirtBar (fun w => wirt (fun u => star (η u) ⬝ᵥ t u) w v) z v =
      star (vectorWirt t z v) ⬝ᵥ D z *ᵥ vectorWirt t z v +
      star (t z) ⬝ᵥ
        (-directionMatrixWirtBar (fun w => directionMatrixWirt D w v) z v +
          directionMatrixWirt D z v * (D z)⁻¹ * directionMatrixWirtBar D z v) *ᵥ t z := by
  have hDd (a b : Fin r) := ((hD a b).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have htd (a : Fin r) := ((ht a).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have htW (a : Fin r) : ContDiffOn ℝ ∞ (fun w => vectorWirt t w v a) U :=
    wirt_contDiffOn hU _ (ht a) v
  have htWd (a : Fin r) := ((htW a).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hV (a : Fin r) : ContDiffOn ℝ ∞ (fun w => (D w *ᵥ vectorWirt t w v) a) U := by
    change ContDiffOn ℝ ∞ (fun w => ∑ b, D w a b * vectorWirt t w v b) U
    exact ContDiffOn.sum fun b _ => (hD a b).mul (htW b)
  have he : (fun w => wirt (fun u => star (η u) ⬝ᵥ t u) w v) =ᶠ[𝓝 z]
      (fun w => star (t w) ⬝ᵥ D w *ᵥ vectorWirt t w v) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirt_dual_pairing_lowered D η t w v (hPos w hw).isHermitian (hLower w hw)
      (fun a => (hη a w hw).differentiableAt (hU.mem_nhds hw))
      (fun a => ((ht a).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
  have hEq : wirtBar (fun w => wirt (fun u => star (η u) ⬝ᵥ t u) w v) z v =
      wirtBar (fun w => star (t w) ⬝ᵥ D w *ᵥ vectorWirt t w v) z v := by
    unfold wirtBar
    rw [he.fderiv_eq]
  rw [hEq, wirtBar_star_dotProduct t (fun w => D w *ᵥ vectorWirt t w v) z v htd
    (fun a => ((hV a).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    vectorWirtBar_mulVec D (fun w => vectorWirt t w v) z v hDd htWd]
  apply dualBochner_loweringAlgebra (D z) (directionMatrixWirt D z v)
    (directionMatrixWirtBar D z v)
    (directionMatrixWirtBar (fun w => directionMatrixWirt D w v) z v) (hPos z hz)
  · have hb := vectorWirtBar_lowering hU D t η hLower z v hz hDd htd
    rw [vectorWirtBar_holomorphic_zero hU η hη z v hz] at hb
    exact hb
  · exact vectorLowering_secondDerivative hU D t η hD ht hη hLower z v hz

end Yau.NodeProofs.D02Aux
