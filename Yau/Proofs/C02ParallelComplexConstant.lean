import Yau.Proofs.C02ParallelComplexDerivative
import Yau.Proofs.C02ParallelComplexOrigin
import Yau.Proofs.C02RadialConstancy

/-! Kähler compatibility and radial parallelity identify the actual
transported target complex structure with the fixed source structure. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normalParallelComplex_eq_standard (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (x : ComplexVector n) :
    normalParallelComplex g p U hU x = complexStructureCLM n :=
  (eq_origin_of_radial_fderiv_zero ((normalParallelComplex_smooth g p U hU).differentiable (by simp))
    (normalParallelComplex_radial_fderiv g p U hU) x).trans (normalParallelComplex_zero g p U hU)

theorem normalParallelCoefficients_I (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ)
    (c : M.Carrier) (x z : ComplexVector n)
    (hx : normalRealMap g p U x ∈ (chartAt (ComplexVector n) c).source) :
    normalParallelCoefficients g p U hU c x (Complex.I • z) =
      Complex.I • normalParallelCoefficients g p U hU c x z := by
  have h := normalParallelComplex_reconstruct g p U hU c x z hx
  have heq : normalParallelComplexInChart g p U hU c x = complexStructureCLM n :=
    (normalParallelComplex_eq_chart g p U hU c x hx).symm.trans (normalParallelComplex_eq_standard g p U hU x)
  rw [heq] at h
  exact h

end Yau.Blueprint.C02Proof
