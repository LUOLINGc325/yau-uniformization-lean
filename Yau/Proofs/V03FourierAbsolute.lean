import Yau.Proofs.V03FourierRapidDecay
import Yau.Proofs.V03PeriodicCircle
import Mathlib.Analysis.PSeries

/-! Absolute Fourier summability and native pointwise reconstruction for
an actual smooth periodic trace. -/

open scoped Topology ContDiff
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleFourier_summable {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) : Summable (circleFourier u) := by
  obtain ⟨C, hC0, hC⟩ := circleFourier_rapid_decay hu hp 2
  have hs : Summable (fun k : ℤ => (((k : ℝ) ^ 2)⁻¹ * C)) := by
    simpa only [one_div] using
      (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_right C
  apply Summable.of_norm_bounded_eventually hs
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with k hk
  simpa only [inv_pow, sq_abs] using hC k hk

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem circleFourier_reconstruction {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u (2 * Real.pi)) (θ : ℝ) :
    HasSum (fun k : ℤ => circleFourier u k * fourier k (θ : AddCircle (2 * Real.pi))) (u θ) := by
  let f : C(AddCircle (2 * Real.pi), ℂ) := ⟨hp.lift, periodic_lift_continuous hp hu.continuous⟩
  have hfu : (f : AddCircle (2 * Real.pi) → ℂ) = hp.lift := rfl
  have hs : Summable (fourierCoeff f) := by
    apply (circleFourier_summable hu hp).congr
    intro k
    simpa only [hfu] using circleFourier_eq_periodic_lift hp k
  have hh := has_pointwise_sum_fourier_series_of_summable hs (θ : AddCircle (2 * Real.pi))
  simpa only [hfu, ← circleFourier_eq_periodic_lift hp, smul_eq_mul,
    Function.Periodic.lift_coe] using hh

end Yau.Blueprint.V03Proof
