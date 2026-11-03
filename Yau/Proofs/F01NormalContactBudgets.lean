import Yau.Proofs.F01PositiveNormalTrace
import Yau.Proofs.F01NormalConformalBudgets
import Yau.Proofs.F01DiagonalHeat

/-! The intrinsic conformal budgets give exactly the native diagonal
gradient and Laplacian budgets needed for the genuine contact estimate. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem conformal_normal_diagonal_trace_bound (g k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ) (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)))
    (B : ℝ)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) • gMat (conformalField g f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField g f) (e 0) - levi f (e 0)).PosSemidef) :
    traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => f (e w)) 0) ≤
      B * traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g f) e 0) := by
  have hv (i : Fin n) : 0 < values i := by
    have hp := pullback_diagonal_pos k e he hei hs i
    simpa only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re] using hp
  have hbound (i : Fin n) : (leviC (fun w => f (e w)) 0 i i).re ≤ B * Real.exp (f (e 0)) :=
    (abs_le.mp (conformal_normal_coordinate_levi_bound g f hf e he hs hvalue B hlo hhi i)).2
  rw [traceWith_real_diagonal values (fun i => (hv i).ne'),
    conformalField_pullbackMatrix, hvalue, hdiag,
    traceWith_real_diagonal_smul_one values (fun i => (hv i).ne')]
  calc
    _ ≤ ∑ i, (values i)⁻¹ * (B * Real.exp (f (e 0))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hbound i) (inv_nonneg.mpr (hv i).le))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem normal_contact_budgets (g k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    (hs : (0 : ComplexVector n) ∈ e.source) (hvalue : pullbackMatrix g e 0 = 1)
    (values : Fin n → ℝ) (hdiag : pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)))
    (j : Fin n) (B G : ℝ) (hgrad : gradNormSq (conformalField g f) f (e 0) ≤ G)
    (hlo : (levi f (e 0) - ((-B : ℝ) : ℂ) • gMat (conformalField g f) (e 0)).PosSemidef)
    (hhi : ((B : ℂ) • gMat (conformalField g f) (e 0) - levi f (e 0)).PosSemidef) :
    let τ := traceWith (pullbackMatrix k e 0) (pullbackMatrix (conformalField g f) e 0)
    0 < τ ∧ diagonalGradientNorm values (fun w => f (e w)) 0 ≤ G * τ ∧
      traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => f (e w)) 0) ≤ B * τ := by
  have hτ := conformal_normal_trace_pos g k f e he hei hs hvalue values hdiag j
  have hd := conformal_normal_gradient_le_trace g k f hf e he hei hs hvalue values hdiag
  have htrace := conformal_normal_diagonal_trace_bound g k f hf e he hei hs hvalue values hdiag B hlo hhi
  refine ⟨hτ, ?_, htrace⟩
  change dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
    (WithLp.toLp 2 (fun i => wirt (fun w => (f (e w) : ℂ)) 0 (stdVec i))) ≤ _
  rw [← hdiag]
  exact hd.trans (by nlinarith [mul_le_mul_of_nonneg_left hgrad hτ.le])

end Yau.NodeProofs.F01Aux
