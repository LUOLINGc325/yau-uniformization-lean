import Yau.Proofs.V03GagliardoLipschitz
import Yau.Proofs.V03GagliardoProduct
import Yau.Proofs.V03PeriodicCircle

/-! The native circular difference-quotient calculus applies to the exact
boundaryDSq definition of the original contract. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem boundaryDSq_eq_circleGagliardo {u : ℝ → ℂ} (hu : Continuous u)
    (hp : Function.Periodic u (2 * Real.pi)) :
    boundaryDSq (fun θ (_ : Unit) => u θ) = circleGagliardo hp.lift := by
  rw [circleGagliardo_eq_dirichlet (periodic_lift_continuous hp hu)]
  exact circleDirichlet_periodic_lift hp

theorem boundaryDSq_le_of_difference_bound {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hup : Function.Periodic u (2 * Real.pi)) (hvp : Function.Periodic v (2 * Real.pi))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ θ t, ‖v θ - v t‖ ≤ C * ‖u θ - u t‖) :
    boundaryDSq (fun θ (_ : Unit) => v θ) ≤
      ENNReal.ofReal (C ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ) := by
  rw [boundaryDSq_eq_circleGagliardo hu hup, boundaryDSq_eq_circleGagliardo hv hvp,
    circleGagliardo_eq_dirichlet (periodic_lift_continuous hup hu),
    circleGagliardo_eq_dirichlet (periodic_lift_continuous hvp hv)]
  apply circleDirichlet_le_of_difference_bound (periodic_lift_continuous hup hu)
    (periodic_lift_continuous hvp hv) hC
  intro x y
  induction x using Quotient.inductionOn' with
  | h θ =>
      induction y using Quotient.inductionOn' with
      | h t => exact hbound θ t

theorem boundaryDSq_mul_le {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hup : Function.Periodic u (2 * Real.pi)) (hvp : Function.Periodic v (2 * Real.pi))
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (huM : ∀ θ, ‖u θ‖ ≤ M) (hvN : ∀ θ, ‖v θ‖ ≤ N) :
    boundaryDSq (fun θ (_ : Unit) => u θ * v θ) ≤
      ENNReal.ofReal (2 * N ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ) +
      ENNReal.ofReal (2 * M ^ 2) * boundaryDSq (fun θ (_ : Unit) => v θ) := by
  have hprod : Function.Periodic (fun θ => u θ * v θ) (2 * Real.pi) := hup.mul hvp
  have hlift : hprod.lift = fun x => hup.lift x * hvp.lift x := by
    funext x
    induction x using Quotient.inductionOn' with
    | h θ => rfl
  rw [boundaryDSq_eq_circleGagliardo (u := fun θ => u θ * v θ) (hu.mul hv) hprod,
    circleGagliardo_eq_dirichlet (periodic_lift_continuous hprod (hu.mul hv)), hlift,
    boundaryDSq_eq_circleGagliardo hu hup, boundaryDSq_eq_circleGagliardo hv hvp,
    circleGagliardo_eq_dirichlet (periodic_lift_continuous hup hu),
    circleGagliardo_eq_dirichlet (periodic_lift_continuous hvp hv)]
  apply circleDirichlet_mul_le (periodic_lift_continuous hup hu) (periodic_lift_continuous hvp hv) hM hN
  · intro x
    induction x using Quotient.inductionOn' with
    | h θ => exact huM θ
  · intro x
    induction x using Quotient.inductionOn' with
    | h θ => exact hvN θ

end Yau.Blueprint.V03Proof
