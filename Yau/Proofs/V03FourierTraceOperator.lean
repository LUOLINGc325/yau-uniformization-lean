import Yau.Proofs.V03IntervalPeriodicLp
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Each original Fourier coefficient is a bounded complex-linear
functional on the native compact interval trace. -/

open scoped Topology lp
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def intervalFourierCoeffL (k : ℤ) : C(BoundaryAngleInterval, ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).comp
    (fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp intervalCircleLpL)

theorem intervalFourierCoeffL_apply (k : ℤ) {u : ℝ → ℂ}
    (hp : Function.Periodic u (2 * Real.pi)) (f : C(BoundaryAngleInterval, ℂ))
    (hf : ∀ θ : BoundaryAngleInterval, f θ = u θ) :
    intervalFourierCoeffL k f = circleFourier u k := by
  change fourierBasis.repr (intervalCircleLpL f) k = _
  rw [fourierBasis_repr, intervalCircleLpL_apply]
  exact intervalTraceLp_fourierCoeff hp f hf k

end Yau.Blueprint.V03Proof
