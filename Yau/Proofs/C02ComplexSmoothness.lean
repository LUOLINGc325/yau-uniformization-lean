import Yau.Proofs.C02ComplexDifferential
import Yau.LeafProofs.L17HolomorphicRegularity

/-! Actual real differentiability and Cauchy--Riemann identities imply
complex infinite-order smoothness on the same original open domain. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem complex_contDiffOn_of_real_CauchyRiemann {O : Set E} (hO : IsOpen O)
    {f : E → F} (hf : ∀ x ∈ O, DifferentiableAt ℝ f x)
    (hI : ∀ x ∈ O, ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    ContDiffOn ℂ ∞ f O := by
  apply Yau.LeafProofs.L17Holomorphic.contDiffOn_of_complexDiff hO
  intro x hx
  exact (hasComplexFDerivAt_of_real_commutes_I (hf x hx) (hI x hx)).differentiableAt.differentiableWithinAt

end Yau.Blueprint.C02Proof
