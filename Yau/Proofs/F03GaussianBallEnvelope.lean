import Mathlib

/-! A measured Gaussian is controlled by actual masses of unit-step radial sublevels. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Yau.Proofs.F03Aux

theorem gaussian_lintegral_le_ball_mass_series {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ x,0 ≤ r x)
    {c : ℝ} (hc : 0 ≤ c) :
    (∫⁻ x,ENNReal.ofReal (Real.exp (-c*(r x)^2)) ∂μ) ≤
      ∑' j : ℕ,ENNReal.ofReal (Real.exp (-c*(j : ℝ)^2))*μ {x | r x<(j : ℝ)+1} := by
  let E : ℕ → Set α := fun j => {x | r x<(j : ℝ)+1}
  let F : ℕ → α → ℝ≥0∞ := fun j => (E j).indicator
    (fun _ => ENNReal.ofReal (Real.exp (-c*(j : ℝ)^2)))
  have hE (j : ℕ) : MeasurableSet (E j) := measurableSet_lt hr measurable_const
  have hF (j : ℕ) : AEMeasurable (F j) μ := (measurable_const.indicator (hE j)).aemeasurable
  have hEnvelope (x : α) : ENNReal.ofReal (Real.exp (-c*(r x)^2)) ≤ ∑' j : ℕ,F j x := by
    let j := Nat.floor (r x)
    have hj : (j : ℝ) ≤ r x := Nat.floor_le (hr0 x)
    have hx : x ∈ E j := Nat.lt_floor_add_one (r x)
    have hsq : (j : ℝ)^2 ≤ (r x)^2 := pow_le_pow_left₀ (Nat.cast_nonneg j) hj 2
    have hExp : Real.exp (-c*(r x)^2) ≤ Real.exp (-c*(j : ℝ)^2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc))
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-c*(j : ℝ)^2)) := ENNReal.ofReal_le_ofReal hExp
      _ = F j x := by simp only [F,indicator_of_mem hx]
      _ ≤ ∑' k : ℕ,F k x := ENNReal.le_tsum (f := fun k : ℕ => F k x) j
  calc
    _ ≤ ∫⁻ x,∑' j : ℕ,F j x ∂μ := lintegral_mono hEnvelope
    _ = ∑' j : ℕ,∫⁻ x,F j x ∂μ := lintegral_tsum hF
    _ = _ := by
      congr 1
      funext j
      exact lintegral_indicator_const (hE j) _

end Yau.Proofs.F03Aux
