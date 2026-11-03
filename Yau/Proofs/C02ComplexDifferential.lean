import Yau.LeafProofs.L21ComplexLinear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! The Cauchy--Riemann identity for the actual real derivative gives
the actual complex derivative, with no additional differentiability premise. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L21Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasComplexFDerivAt_of_real_commutes_I {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    HasFDerivAt f (complexLinearOfReal (fderiv ℝ f x) hI) x := by
  apply hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem complex_fderiv_restrictScalars_of_real_commutes_I {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    (fderiv ℂ f x).restrictScalars ℝ = fderiv ℝ f x := by
  rw [(hasComplexFDerivAt_of_real_commutes_I hf hI).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rfl

end Yau.Blueprint.C02Proof
