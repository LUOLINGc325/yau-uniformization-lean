import Yau.Proofs.F01FlowFirstExchange
import Yau.Proofs.F01MetricEntryLog

/-! The actual normalized matrix row is the logarithmic diagonal gradient
minus exactly the masked conformal gradient in the paper's chosen direction. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def maskedCoordinate (a : Fin n) (ξ : Fin n → ℂ) (i : Fin n) : ℂ :=
  if i = a then 0 else ξ i

theorem flow_normalized_row_gradient (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField g f) x -
      (t : ℂ) • ricci (conformalField g f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0) (a : Fin n) :
    let q := (pullbackMatrix k e 0 a a).re
    (fun i => wirt (fun w => pullbackMatrix k e w a i) 0 (stdVec a) / (q : ℂ)) =
      (fun i => wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 (stdVec i) -
        ((Real.exp (f (e 0)) : ℂ) / (q : ℂ)) *
          maskedCoordinate a (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)) i) := by
  dsimp only
  funext i
  by_cases hi : i = a
  · subst i
    rw [pullback_diagonal_log_wirt k hk e he hei hs0 a (stdVec a)]
    simp [maskedCoordinate, div_eq_mul_inv, mul_comm]
  · rw [conformal_flow_offdiagonal_first_exchange g k hg hk f hf u hu t hpot e he hei
        hs0 hvalue hjet i a hi,
      pullback_diagonal_log_wirt k hk e he hei hs0 a (stdVec i)]
    simp only [maskedCoordinate, if_neg hi]
    ring

end Yau.NodeProofs.F01Aux
