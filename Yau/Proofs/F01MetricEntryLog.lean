import Yau.Proofs.F01ConformalGradient
import Yau.Proofs.F01ChartGramSmooth
import Yau.Proofs.F01DiagonalRayleigh

/-! Actual diagonal metric coefficients are real and positive, and their
real logarithm has the genuine reciprocal Wirtinger derivative. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem pullback_diagonal_real (g : HermitianField M) (e : ComplexVector n → M.Carrier)
    (z : ComplexVector n) (a : Fin n) :
    (((pullbackMatrix g e z a a).re : ℝ) : ℂ) = pullbackMatrix g e z a a := by
  have hh := congrArg Complex.im ((pullbackMatrix_isHermitian g e z).apply a a)
  simp only [Complex.star_def, Complex.conj_im] at hh
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

theorem pullback_diagonal_pos (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (a : Fin n) :
    0 < (pullbackMatrix g e z a a).re := by
  have hs : (Pi.single a (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
    intro h
    have hh := congrFun h a
    simpa using hh
  simpa only [matrixQuadraticValue_single] using
    matrixQuadraticValue_pos (pullbackMatrix_posDef g e he hei hz) hs

theorem pullback_diagonal_log_wirt (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (a : Fin n) (v : ComplexVector n) :
    wirt (fun w => (Real.log (pullbackMatrix g e w a a).re : ℂ)) z v =
      (((pullbackMatrix g e z a a).re : ℝ) : ℂ)⁻¹ *
        wirt (fun w => pullbackMatrix g e w a a) z v := by
  have hd : DifferentiableAt ℝ (fun w => (pullbackMatrix g e w a a).re) z :=
    Complex.reCLM.differentiableAt.comp z
      ((pullbackMatrix_entry_contDiffAt g hg e he hz a a).differentiableAt (by simp))
  have hp := pullback_diagonal_pos g e he hei hz a
  have hh := wirt_ofReal_scalar_comp hd (Real.hasDerivAt_log hp.ne') v
  have hreal : (fun w => (((pullbackMatrix g e w a a).re : ℝ) : ℂ)) =
      (fun w => pullbackMatrix g e w a a) := funext (fun w => pullback_diagonal_real g e w a)
  rw [hreal, Complex.ofReal_inv] at hh
  exact hh

end Yau.NodeProofs.F01Aux
