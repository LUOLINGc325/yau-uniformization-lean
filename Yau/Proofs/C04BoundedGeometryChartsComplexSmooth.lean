import Yau.Proofs.C04BoundedGeometryChartsComplexDerivative
import Yau.Proofs.V03HolomorphicSmooth

/-! The first-order real complex-equation bridge followed by the accepted finite-dimensional Cauchy theorem. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem contDiffOn_complex_of_real_and_I {O : Set E} (hO : IsOpen O) (f : E → F)
    (hf : ContDiffOn ℝ ∞ f O)
    (hI : ∀ x ∈ O, ∀ v, fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v) :
    ContDiffOn ℂ ∞ f O := by
  apply Yau.Blueprint.V03Proof.complex_holomorphic_contDiffOn hO
  intro x hx
  exact (differentiableAt_complex_of_real_and_I f x
    ((hf.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)) (hI x hx)).differentiableWithinAt

end Yau.Proofs.C04ChartsAux
