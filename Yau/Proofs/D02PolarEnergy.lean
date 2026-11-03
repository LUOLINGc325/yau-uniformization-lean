import Yau.Proofs.D02PhysicalScaling
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Polar Tonelli for the actual ordinary planar area used by D02.
All radial energies are nonnegative extended integrals, so no boundary
extension or integrability assumption is needed in the change of variables. -/

open scoped ENNReal
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

def polarRay (r θ : ℝ) : ℂ := Complex.polarCoord.symm (r, θ)

theorem polarRay_norm (r θ : ℝ) : ‖polarRay r θ‖ = |r| :=
  Complex.norm_polarCoord_symm (r, θ)

theorem polarRay_continuous : Continuous (fun p : ℝ × ℝ => polarRay p.1 p.2) := by
  simp only [polarRay, Complex.polarCoord_symm_apply]
  fun_prop

/-- Exact polar integration of a measurable density on a genuine annulus. -/
theorem annulus_lintegral_polar (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, Q z) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo a b,
        ENNReal.ofReal r * Q (polarRay r θ) := by
  let A : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}
  let D : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * Q (polarRay p.1 p.2)
  have hA : MeasurableSet A :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hQ.comp polarRay_continuous.measurable)
  have hchange : (∫⁻ z in A, Q z) = ∫⁻ p in D, G p := by
    rw [← lintegral_indicator hA, ← Complex.lintegral_comp_polarCoord_symm]
    change (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * A.indicator Q (Complex.polarCoord.symm p)) = ∫⁻ p in D, G p
    have hT : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
    have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioo
    rw [← lintegral_indicator hT, ← lintegral_indicator hD]
    apply lintegral_congr
    intro p
    by_cases hpD : p ∈ D
    · have hpT : p ∈ polarCoord.target := ⟨ha.trans hpD.1.1, hpD.2⟩
      have hpA : Complex.polarCoord.symm p ∈ A := by
        change a < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ < b
        rw [Complex.norm_polarCoord_symm, abs_of_pos (ha.trans hpD.1.1)]
        exact hpD.1
      rw [indicator_of_mem hpT, indicator_of_mem hpD, indicator_of_mem hpA]
      rfl
    · by_cases hpT : p ∈ polarCoord.target
      · have hpA : Complex.polarCoord.symm p ∉ A := by
          intro hpA
          apply hpD
          refine ⟨?_, hpT.2⟩
          change a < p.1 ∧ p.1 < b
          simpa only [A, mem_ofPred_eq, Complex.norm_polarCoord_symm,
            abs_of_pos (show 0 < p.1 from hpT.1)] using hpA
        rw [indicator_of_mem hpT, indicator_of_notMem hpD,
          indicator_of_notMem hpA, mul_zero]
      · rw [indicator_of_notMem hpT, indicator_of_notMem hpD]
  rw [hchange, Measure.volume_eq_prod]
  exact setLIntegral_prod_symm G hG.aemeasurable

/-- The energy of the outer half of one radial ray, with its area Jacobian. -/
def radialEnergy (Q : ℂ → ℝ≥0∞) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (1 / 2 : ℝ) 1, ENNReal.ofReal r * Q (polarRay r θ)

theorem radialEnergy_measurable (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q) :
    Measurable (radialEnergy Q) := by
  change Measurable (fun θ => ∫⁻ r, ENNReal.ofReal r * Q (polarRay r θ)
    ∂(volume.restrict (Ioo (1 / 2 : ℝ) 1)))
  have hG : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * Q (polarRay p.1 p.2)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hQ.comp polarRay_continuous.measurable)
  exact Measurable.lintegral_prod_left' (μ := volume.restrict (Ioo (1 / 2 : ℝ) 1)) hG

/-- The total radial energy is bounded by the original open-disc area density. -/
theorem radialEnergy_total_le (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, radialEnergy Q θ) ≤
      ∫⁻ z in Metric.ball (0 : ℂ) 1, Q z := by
  unfold radialEnergy
  rw [← annulus_lintegral_polar Q hQ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)]
  exact lintegral_mono_set (fun z hz => by simpa [Metric.mem_ball, dist_zero_right] using hz.2)

end Yau.NodeProofs.D02Aux
