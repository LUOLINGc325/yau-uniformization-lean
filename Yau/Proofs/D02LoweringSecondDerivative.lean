import Yau.Proofs.D02HolomorphicWirtinger

/-! Differentiating the actual lowering identity twice supplies the mixed
term used in the dual Bochner identity. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs.L14Aux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {r : ℕ}

theorem vectorWirtBar_add (t s : V → Fin r → ℂ) (z v : V)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z)
    (hs : ∀ a, DifferentiableAt ℝ (fun w => s w a) z) :
    vectorWirtBar (fun w => t w + s w) z v = vectorWirtBar t z v + vectorWirtBar s z v := by
  funext a
  change wirtBar (fun w => t w a + s w a) z v = _
  rw [wirtBar_add_rule _ _ z v (ht a) (hs a)]
  rfl

theorem vectorLowering_secondDerivative {U : Set V} (hU : IsOpen U)
    (D : V → Matrix (Fin r) (Fin r) ℂ) (t η : V → Fin r → ℂ)
    (hD : ∀ a b, ContDiffOn ℝ ∞ (fun w => D w a b) U)
    (ht : ∀ a, ContDiffOn ℝ ∞ (fun w => t w a) U)
    (hη : ∀ a, DifferentiableOn ℂ (fun w => η w a) U)
    (hLower : ∀ w ∈ U, D w *ᵥ t w = η w) (z v : V) (hz : z ∈ U) :
    directionMatrixWirtBar D z v *ᵥ vectorWirt t z v +
        D z *ᵥ vectorWirtBar (fun w => vectorWirt t w v) z v =
      -(directionMatrixWirtBar (fun w => directionMatrixWirt D w v) z v *ᵥ t z +
        directionMatrixWirt D z v *ᵥ vectorWirtBar t z v) := by
  have hDd (a b : Fin r) := ((hD a b).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have htd (a : Fin r) := ((ht a).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hDW (a b : Fin r) : ContDiffOn ℝ ∞
      (fun w => directionMatrixWirt D w v a b) U :=
    wirt_contDiffOn hU _ (hD a b) v
  have htW (a : Fin r) : ContDiffOn ℝ ∞ (fun w => vectorWirt t w v a) U :=
    wirt_contDiffOn hU _ (ht a) v
  have hDWd (a b : Fin r) := ((hDW a b).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have htWd (a : Fin r) := ((htW a).contDiffAt (hU.mem_nhds hz)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hp (a : Fin r) : ContDiffOn ℝ ∞
      (fun w => (directionMatrixWirt D w v *ᵥ t w) a) U := by
    change ContDiffOn ℝ ∞ (fun w => ∑ b, directionMatrixWirt D w v a b * t w b) U
    exact ContDiffOn.sum fun b _ => (hDW a b).mul (ht b)
  have hq (a : Fin r) : ContDiffOn ℝ ∞
      (fun w => (D w *ᵥ vectorWirt t w v) a) U := by
    change ContDiffOn ℝ ∞ (fun w => ∑ b, D w a b * vectorWirt t w v b) U
    exact ContDiffOn.sum fun b _ => (hD a b).mul (htW b)
  have he : (fun w => directionMatrixWirt D w v *ᵥ t w + D w *ᵥ vectorWirt t w v) =ᶠ[𝓝 z]
      (fun w => vectorWirt η w v) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact vectorWirt_lowering hU D t η hLower w v hw
      (fun a b => ((hD a b).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
      (fun a => ((ht a).contDiffAt (hU.mem_nhds hw)).differentiableAt (by simp))
  have hbar : vectorWirtBar
      (fun w => directionMatrixWirt D w v *ᵥ t w + D w *ᵥ vectorWirt t w v) z v = 0 := by
    calc
      _ = vectorWirtBar (fun w => vectorWirt η w v) z v := by
        funext a
        have ha : (fun w => (directionMatrixWirt D w v *ᵥ t w + D w *ᵥ vectorWirt t w v) a)
            =ᶠ[𝓝 z] (fun w => vectorWirt η w v a) := he.mono (fun _ hw => congrFun hw a)
        unfold vectorWirtBar wirtBar
        rw [ha.fderiv_eq]
      _ = 0 := vectorWirtBar_vectorWirt_holomorphic_zero hU η hη z v hz
  rw [vectorWirtBar_add _ _ z v
    (fun a => ((hp a).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
    (fun a => ((hq a).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)),
    vectorWirtBar_mulVec _ _ z v hDWd htd, vectorWirtBar_mulVec _ _ z v hDd htWd] at hbar
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hbar

end Yau.NodeProofs.D02Aux
