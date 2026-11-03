import Yau.Proofs.D02PolarEnergy
import Yau.Proofs.D02AreaDensity

/-! One explicit radial-energy threshold and a measurable set of at least
half the available angles, for every disc in the original area family. -/

open scoped ENNReal
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

def radialEnergyThreshold (A : ℝ) : ℝ := (max A 0 + 1) / Real.pi

theorem radialEnergyThreshold_pos (A : ℝ) : 0 < radialEnergyThreshold A := by
  unfold radialEnergyThreshold
  positivity

def goodAngles (Q : ℂ → ℝ≥0∞) (A : ℝ) : Set ℝ :=
  Ioo (-Real.pi) Real.pi ∩ {θ | radialEnergy Q θ < ENNReal.ofReal (radialEnergyThreshold A)}

theorem goodAngles_measurable (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q) (A : ℝ) :
    MeasurableSet (goodAngles Q A) :=
  measurableSet_Ioo.inter (measurableSet_lt (radialEnergy_measurable Q hQ) measurable_const)

/-- Markov's inequality keeps an angular set of measure at least π.
The additive one makes the threshold positive even for negative area parameters. -/
theorem goodAngles_volume_lower (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q) (A : ℝ)
    (harea : (∫⁻ z in Metric.ball (0 : ℂ) 1, Q z) ≤ ENNReal.ofReal A) :
    ENNReal.ofReal Real.pi ≤ volume (goodAngles Q A) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  let ε : ℝ := radialEnergyThreshold A
  have hε : 0 < ε := radialEnergyThreshold_pos A
  have hbound : (∫⁻ θ, radialEnergy Q θ ∂μ) ≤ ENNReal.ofReal (max A 0) :=
    (radialEnergy_total_le Q hQ).trans (harea.trans (ENNReal.ofReal_le_ofReal (le_max_left A 0)))
  have hbad : μ {θ | ENNReal.ofReal ε ≤ radialEnergy Q θ} ≤ ENNReal.ofReal Real.pi := by
    apply (meas_ge_le_lintegral_div (radialEnergy_measurable Q hQ).aemeasurable
      (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top).trans
    apply (ENNReal.div_le_div_right hbound _).trans
    rw [← ENNReal.ofReal_div_of_pos hε]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hε).mpr
    dsimp only [ε, radialEnergyThreshold]
    have hp := Real.pi_pos.ne'
    field_simp
    linarith
  have hmass : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_Ioo]
    congr 1
    ring
  have hcompl : {θ | radialEnergy Q θ < ENNReal.ofReal ε} =
      Set.univ \ {θ | ENNReal.ofReal ε ≤ radialEnergy Q θ} := by
    ext θ
    simp
  have hgood : μ {θ | radialEnergy Q θ < ENNReal.ofReal ε} = volume (goodAngles Q A) := by
    rw [Measure.restrict_apply (measurableSet_lt (radialEnergy_measurable Q hQ) measurable_const)]
    exact congrArg volume (Set.inter_comm _ _)
  rw [← hgood, hcompl]
  calc
    ENNReal.ofReal Real.pi =
        ENNReal.ofReal (2 * Real.pi) - ENNReal.ofReal Real.pi := by
      rw [← ENNReal.ofReal_sub _ Real.pi_pos.le]
      congr 1
      ring
    _ ≤ μ Set.univ - μ {θ | ENNReal.ofReal ε ≤ radialEnergy Q θ} := by
      rw [hmass]
      exact tsub_le_tsub_left hbad _
    _ ≤ _ := le_measure_sdiff

/-- The set and its lower area bound are attached to the actual disc density. -/
theorem disc_goodAngles {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) (A : ℝ)
    (harea : discArea g.form f ≤ ENNReal.ofReal A) :
    MeasurableSet (goodAngles (discEnergyDensity g.form f) A) ∧
      ENNReal.ofReal Real.pi ≤ volume (goodAngles (discEnergyDensity g.form f) A) ∧
      ∀ θ ∈ goodAngles (discEnergyDensity g.form f) A,
        radialEnergy (discEnergyDensity g.form f) θ < ENNReal.ofReal (radialEnergyThreshold A) := by
  have hQ := discEnergyDensity_measurable g hf
  refine ⟨goodAngles_measurable _ hQ A, goodAngles_volume_lower _ hQ A ?_, fun θ hθ => hθ.2⟩
  rw [discEnergyDensity_integral g.form hf]
  exact harea

end Yau.NodeProofs.D02Aux
