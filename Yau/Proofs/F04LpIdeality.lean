import Yau.Proofs.F03L2Restriction
import Yau.Proofs.F04PositiveScalarPairing

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

variable {X : Type*} [MeasurableSpace X]

theorem l2Restriction_posPart (μ : Measure X) (O : Set X) (f : Lp ℝ 2 μ) :
    l2Restriction μ O (Lp.posPart f) = Lp.posPart (l2Restriction μ O f) := by
  apply Lp.ext
  filter_upwards [restrictL2_coe μ O (Lp.posPart f),
    ae_restrict_of_ae (Lp.coeFn_posPart f),
    Lp.coeFn_posPart (l2Restriction μ O f), restrictL2_coe μ O f] with x hr hp hpr hrf
  change restrictL2 μ O (Lp.posPart f) x = _
  rw [hr, hp, hpr]
  change max (f x) 0 = max (restrictL2 μ O f x) 0
  rw [hrf]

/-- Positive truncation against a nonnegative ambient shift commutes with
the genuine L2 zero extension of the supported input. -/
theorem l2ZeroExtension_shift_posPart (μ : Measure X) (O : Set X) (hO : MeasurableSet O)
    (f : Lp ℝ 2 (μ.restrict O)) (q : Lp ℝ 2 μ) (hq : ∀ᵐ x ∂μ, 0 ≤ q x) :
    l2ZeroExtension μ O hO (Lp.posPart (f - l2Restriction μ O q)) =
      Lp.posPart (l2ZeroExtension μ O hO f - q) := by
  have hi : ∀ᵐ x ∂μ.restrict O,
      Lp.posPart (f - l2Restriction μ O q) x = max (f x - q x) 0 := by
    filter_upwards [Lp.coeFn_posPart (f - l2Restriction μ O q),
      Lp.coeFn_sub f (l2Restriction μ O q), restrictL2_coe μ O q] with x hp hs hr
    rw [hp, hs]
    change max (f x - restrictL2 μ O q x) 0 = max (f x - q x) 0
    rw [hr]
  have hig := (ae_eq_restrict_iff_indicator_ae_eq hO).mp hi
  apply Lp.ext
  filter_upwards [extendL2_coe μ O hO (Lp.posPart (f - l2Restriction μ O q)),
    extendL2_coe μ O hO f,
    Lp.coeFn_posPart (l2ZeroExtension μ O hO f - q),
    Lp.coeFn_sub (l2ZeroExtension μ O hO f) q, hig, hq] with x hw hf hp hs hi hq
  change extendL2 μ O hO (Lp.posPart (f - l2Restriction μ O q)) x = _
  rw [hw, hi, hp, hs]
  simp only [Pi.sub_apply]
  change O.indicator (fun x => max (f x - q x) 0) x =
    max (extendL2 μ O hO f x - q x) 0
  rw [hf]
  by_cases hx : x ∈ O
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, zero_sub]
    exact (max_eq_right (neg_nonpos.mpr hq)).symm

end Yau.F04Proof
