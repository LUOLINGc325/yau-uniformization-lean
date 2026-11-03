import Yau.Proofs.V03IntervalCircleLp
import Yau.Proofs.V03PeriodicCircle

/-! On actual periodic traces, the bounded interval-to-L² map has exactly
the original circle representative and original normalized coefficients. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem intervalTraceLp_periodic_ae {u : ℝ → ℂ}
    (hp : Function.Periodic u (2 * Real.pi)) (f : C(BoundaryAngleInterval, ℂ))
    (hf : ∀ θ : BoundaryAngleInterval, f θ = u θ) :
    (intervalTraceLp f : AddCircle (2 * Real.pi) → ℂ) =ᵐ[haarAddCircle] hp.lift := by
  filter_upwards [(intervalTrace_memLp f).coeFn_toLp] with x hx
  calc
    intervalTraceLp f x = f (circleIntervalRepresentative x) := hx
    _ = u (circleIntervalRepresentative x) := hf _
    _ = hp.lift (((circleIntervalRepresentative x : ℝ)) : AddCircle (2 * Real.pi)) :=
      (Function.Periodic.lift_coe hp _).symm
    _ = hp.lift x := congrArg hp.lift (coe_circleIntervalRepresentative x)

theorem intervalTraceLp_fourierCoeff {u : ℝ → ℂ}
    (hp : Function.Periodic u (2 * Real.pi)) (f : C(BoundaryAngleInterval, ℂ))
    (hf : ∀ θ : BoundaryAngleInterval, f θ = u θ) (k : ℤ) :
    fourierCoeff (intervalTraceLp f) k = circleFourier u k := by
  rw [fourierCoeff_congr_ae (intervalTraceLp_periodic_ae hp f hf)]
  exact (circleFourier_eq_periodic_lift hp k).symm

end Yau.Blueprint.V03Proof
