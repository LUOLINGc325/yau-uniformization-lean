import Yau.Proofs.P04PoleChartValues
import Yau.Proofs.P04PoleVanishing

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

theorem poleEpsilon_tendsto_zero (ρ : ℝ) :
    Tendsto (poleEpsilon ρ) atTop (𝓝 0) := by
  change Tendsto (fun j : ℕ => ρ/((j : ℝ)+2)) atTop (𝓝 0)
  simpa only [Function.comp_def,poleEpsilon,Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_const_div_atTop_nhds_zero_nat ρ).comp (tendsto_add_atTop_nat 2)

/-- Fatou passes the SAME regularized bounds to the exact singular power.
At the pole only the nonnegative ENNReal inequality is used. -/
theorem regularized_pole_integrals_bound_singular (z₀ : ComplexVector n)
    (ρ : ℝ) {c : ℝ} (hc : 0 < c) (s : Set (ComplexVector n))
    (b : ComplexVector n → ℂ) (Φ : ComplexVector n → ℝ)
    (hb : AEMeasurable b ((lebesgueC n).restrict s))
    (hΦ : AEMeasurable Φ ((lebesgueC n).restrict s))
    (B : ℝ≥0∞)
    (hbound : ∀ j : ℕ, (∫⁻ z in s, ENNReal.ofReal
      (‖b z‖^2*Real.exp (-Φ z)*(‖z-z₀‖^2+poleEpsilon ρ j^2)^(-c)) ∂lebesgueC n) ≤ B) :
    (∫⁻ z in s, ENNReal.ofReal
      (‖b z‖^2*Real.exp (-Φ z)*‖z-z₀‖^(-2*c)) ∂lebesgueC n) ≤ B := by
  let f : ℕ → ComplexVector n → ℝ≥0∞ := fun j z => ENNReal.ofReal
    (‖b z‖^2*Real.exp (-Φ z)*(‖z-z₀‖^2+poleEpsilon ρ j^2)^(-c))
  have hm (j : ℕ) : AEMeasurable (f j) ((lebesgueC n).restrict s) := by
    have hq : AEMeasurable (fun z : ComplexVector n => ‖z-z₀‖^2+poleEpsilon ρ j^2)
        ((lebesgueC n).restrict s) :=
      (((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).add continuous_const).measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    exact ((hb.norm.pow_const 2).mul (Real.measurable_exp.comp_aemeasurable hΦ.neg)).mul
      (hq.pow_const (-c))
  have hpoint (z : ComplexVector n) :
      ENNReal.ofReal (‖b z‖^2*Real.exp (-Φ z)*‖z-z₀‖^(-2*c)) ≤
        liminf (fun j => f j z) atTop := by
    by_cases hz : z=z₀
    · subst z
      simp only [sub_self,norm_zero,Real.zero_rpow (by linarith : -2*c ≠ 0),mul_zero,
        ENNReal.ofReal_zero]
      exact bot_le
    · have hnorm : ‖z-z₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
      have hq : Tendsto (fun j => ‖z-z₀‖^2+poleEpsilon ρ j^2) atTop (𝓝 (‖z-z₀‖^2)) := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0),add_zero] using
          tendsto_const_nhds.add ((poleEpsilon_tendsto_zero ρ).pow 2)
      have hpow := hq.rpow_const (Or.inl (pow_ne_zero 2 hnorm)) (p := -c)
      have heq : (‖z-z₀‖^2)^(-c)=‖z-z₀‖^(-2*c) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
      have ht : Tendsto (fun j => f j z) atTop
          (𝓝 (ENNReal.ofReal (‖b z‖^2*Real.exp (-Φ z)*‖z-z₀‖^(-2*c)))) := by
        apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        simpa only [heq] using tendsto_const_nhds.mul hpow
      exact ht.liminf_eq.ge
  calc
    _ ≤ ∫⁻ z in s, liminf (fun j => f j z) atTop ∂lebesgueC n := lintegral_mono hpoint
    _ ≤ liminf (fun j => ∫⁻ z in s, f j z ∂lebesgueC n) atTop := lintegral_liminf_le' hm
    _ ≤ limsup (fun j => ∫⁻ z in s, f j z ∂lebesgueC n) atTop := liminf_le_limsup
    _ ≤ B := limsup_le_of_le (h := Eventually.of_forall hbound)

end Yau.Proofs.P04Aux
