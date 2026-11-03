import Yau.Proofs.F01NegativeSquareRow
import Yau.Proofs.F01CorrectedRowGradient
import Yau.Proofs.F01HermitianMatrixJets

/-! The actual negative squared matrix jet dominates precisely the
corrected logarithmic gradient in the paper's fixed normal direction. -/
noncomputable section
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem flow_negative_square_controls_corrected_gradient (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (t : ℝ)
    (hpot : ∀ x, gMat k x = gMat (conformalField g f) x -
      (t : ℂ) • ricci (conformalField g f) x + levi u x)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs0 : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (hjet : ∀ i j, fderiv ℝ (fun w => pullbackMatrix g e w i j) 0 = 0)
    (values : Fin n → ℝ)
    (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ))) (a : Fin n) :
    let q := (pullbackMatrix k e 0 a a).re
    dualNormMat (pullbackMatrix k e 0) (WithLp.toLp 2 (fun i =>
      wirt (fun w => (Real.log (pullbackMatrix k e w a a).re : ℂ)) 0 (stdVec i) -
        ((Real.exp (f (e 0)) : ℂ) / (q : ℂ)) *
          maskedCoordinate a (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i)) i)) ≤
      q⁻¹ * ∑ i, ∑ j, (values i)⁻¹ * (values j)⁻¹ *
        Complex.normSq (wirt (fun w => pullbackMatrix k e w j i) 0 (stdVec a)) := by
  have hvalues (i : Fin n) : 0 < values i := by
    have hh := pullback_diagonal_pos k e he hei hs0 i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hh
  have hqa : (pullbackMatrix k e 0 a a).re = values a := by
    rw [hdiag]
    simp
  have hvec := flow_normalized_row_gradient g k hg hk f hf u hu t hpot e he hei hs0 hvalue hjet a
  dsimp only at hvec
  rw [hqa] at hvec
  have hh := negative_matrix_square_controls_row values hvalues
    (matrixUnbarJet (pullbackMatrix k e) 0 (stdVec a)) a
  rw [← hdiag] at hh
  dsimp only
  rw [hqa, ← hvec]
  exact hh

end Yau.NodeProofs.F01Aux
