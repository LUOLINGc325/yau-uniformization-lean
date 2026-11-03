import Yau.Proofs.V03FourierInnerParseval
import Yau.Proofs.V03PeriodicCircle

/-! Cross-Parseval in the original period-2π normalization. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem periodic_parseval_inner {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hup : Function.Periodic u (2 * Real.pi)) (hvp : Function.Periodic v (2 * Real.pi)) :
    HasSum (fun k : ℤ => star (circleFourier u k) * circleFourier v k)
      (circleFourier (fun θ => star (u θ) * v θ) 0) := by
  have hp : Function.Periodic (fun θ => star (u θ) * v θ) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [hup θ, hvp θ]
  have hlift : hp.lift = (fun x => star (hup.lift x) * hvp.lift x) := by
    funext x
    induction x using Quotient.inductionOn' with
    | h θ => rfl
  have hi : (∫ x : AddCircle (2 * Real.pi), star (hup.lift x) * hvp.lift x ∂haarAddCircle) =
      circleFourier (fun θ => star (u θ) * v θ) 0 := by
    rw [circleFourier_eq_periodic_lift hp, fourierCoeff, hlift]
    simp only [neg_zero, fourier_zero, ContinuousMap.one_apply, one_smul]
  have hh := circle_parseval_inner (periodic_lift_continuous hup hu) (periodic_lift_continuous hvp hv)
  simpa only [← circleFourier_eq_periodic_lift hup, ← circleFourier_eq_periodic_lift hvp, hi] using hh

theorem periodic_parseval_inner_real {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hup : Function.Periodic u (2 * Real.pi)) (hvp : Function.Periodic v (2 * Real.pi)) :
    HasSum (fun k : ℤ => (star (circleFourier u k) * circleFourier v k).re)
      (circleAverage (fun θ => (star (u θ) * v θ).re)) := by
  have hh := (periodic_parseval_inner hu hv hup hvp).mapL Complex.reCLM
  have hi : (circleFourier (fun θ => star (u θ) * v θ) 0).re =
      circleAverage (fun θ => (star (u θ) * v θ).re) := by
    have hint : IntervalIntegrable (fun θ => star (u θ) * v θ) volume 0 (2 * Real.pi) :=
      (hu.star.mul hv).intervalIntegrable _ _
    have hreal := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at hreal
    simp only [circleFourier, Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
      circleAverage]
    rw [Complex.re_ofReal_mul, ← hreal]
  simpa only [Complex.reCLM_apply, hi] using hh

end Yau.Blueprint.V03Proof
