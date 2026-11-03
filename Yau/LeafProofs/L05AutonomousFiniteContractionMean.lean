import Yau.LeafProofs.L05AutonomousFiniteContractionScalar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Basic

open MeasureTheory
open scoped BigOperators

namespace Yau.LeafProofs.L05AutonomousAux

/-- Literal Bochner-integral quasi-triangle inequality for a finite nonnegative family. -/
theorem finite_integral_rpow_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {m : ℕ} (_hm : 0 < m) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (D : Fin m → X → ℝ) (hD : ∀ i, Measurable (D i))
    (hD0 : ∀ i, ∀ᵐ x ∂μ, 0 ≤ D i x)
    (hDI : ∀ i, Integrable (fun x => (D i x) ^ p) μ) :
    Integrable (fun x => (∑ i, D i x) ^ p) μ ∧
    (∫ x, (∑ i, D i x) ^ p ∂μ) ^ (1 / p) ≤
      (m : ℝ) ^ (1 / p - 1) * ∑ i, (∫ x, (D i x) ^ p ∂μ) ^ (1 / p) := by
  classical
  have hD0' : ∀ᵐ x ∂μ, ∀ i, 0 ≤ D i x := ae_all_iff.mpr hD0
  have hsumI : Integrable (fun x => ∑ i, (D i x) ^ p) μ := integrable_finsetSum _ (fun i _ => hDI i)
  have hpow : ∀ᵐ x ∂μ, (∑ i, D i x) ^ p ≤ ∑ i, (D i x) ^ p := by
    filter_upwards [hD0'] with x hx
    exact finite_sum_rpow_le Finset.univ (fun i => D i x) (fun i _ => hx i) hp hp1.le
  have hmeas : Measurable (fun x => (∑ i, D i x) ^ p) :=
    (Finset.measurable_sum _ (fun i _ => hD i)).pow_const p
  have hsum0 : ∀ᵐ x ∂μ, 0 ≤ (∑ i, D i x) ^ p := by
    filter_upwards [hD0'] with x hx
    exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => hx i) _
  have hI : Integrable (fun x => (∑ i, D i x) ^ p) μ :=
    hsumI.mono_nonneg hmeas.aestronglyMeasurable
      hsum0 hpow
  refine ⟨hI, ?_⟩
  have hint : (∫ x, (∑ i, D i x) ^ p ∂μ) ≤ ∑ i, ∫ x, (D i x) ^ p ∂μ := by
    calc
      _ ≤ ∫ x, ∑ i, (D i x) ^ p ∂μ := integral_mono_ae hI hsumI hpow
      _ = _ := integral_finsetSum _ (fun i _ => hDI i)
  calc
    _ ≤ (∑ i, ∫ x, (D i x) ^ p ∂μ) ^ (1 / p) :=
      Real.rpow_le_rpow (integral_nonneg_of_ae hsum0) hint (by positivity)
    _ ≤ _ := by
      simpa using Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Finset.univ
        (f := fun i => ∫ x, (D i x) ^ p ∂μ) (by rw [le_div_iff₀ hp]; linarith : 1 ≤ 1 / p)
        (fun i _ => integral_nonneg_of_ae ((hD0 i).mono fun x hx => Real.rpow_nonneg hx _))

end Yau.LeafProofs.L05AutonomousAux
