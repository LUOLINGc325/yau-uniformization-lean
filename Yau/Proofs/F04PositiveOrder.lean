import Yau.Proofs.F04PositiveScalarPairing

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {X : Type*} [MeasurableSpace X]

theorem lp_posPart_eq_zero_iff (μ : Measure X) (f : Lp ℝ 2 μ) :
    Lp.posPart f = 0 ↔ ∀ᵐ x ∂μ, f x ≤ 0 := by
  constructor
  · intro h
    filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hp hz
    have hx := congrArg (fun a : Lp ℝ 2 μ => a x) h
    rw [hp, hz] at hx
    exact (le_max_left _ _).trans hx.le
  · intro h
    apply Lp.ext
    filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ), h] with x hp hz hx
    rw [hp, hz, max_eq_right hx]
    rfl

theorem lp_posPart_sub_eq_zero_iff (μ : Measure X) (f q : Lp ℝ 2 μ) :
    Lp.posPart (f - q) = 0 ↔ ∀ᵐ x ∂μ, f x ≤ q x := by
  rw [lp_posPart_eq_zero_iff]
  constructor
  · intro h
    filter_upwards [h, Lp.coeFn_sub f q] with x hx hs
    rw [hs, Pi.sub_apply] at hx
    exact sub_nonpos.mp hx
  · intro h
    filter_upwards [h, Lp.coeFn_sub f q] with x hx hs
    rw [hs, Pi.sub_apply]
    exact sub_nonpos.mpr hx

end Yau.F04Proof
