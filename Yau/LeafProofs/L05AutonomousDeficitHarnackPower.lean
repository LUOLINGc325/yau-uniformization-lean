import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

open Filter Set MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L05AutonomousAux

/-- The deficit dominator does not require the upper level M to be nonnegative. -/
theorem auto_deficit_power_bound {M B v p : ℝ} (hp : 0 ≤ p)
    (hv : |v| ≤ B) (hvM : v ≤ M) :
    ‖(M-v)^p‖ ≤ (|M|+B+1)^p := by
  have hnonneg : 0 ≤ M-v := sub_nonneg.mpr hvM
  have hupper : M-v ≤ |M|+B+1 := by
    have hvlow := (abs_le.mp hv).1
    have hM := le_abs_self M
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnonneg p)]
  exact Real.rpow_le_rpow hnonneg hupper hp

/-- Actual almost-everywhere limits retain both the two-sided budget and the exact upper level. -/
theorem auto_deficit_limit_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {M B : ℝ} (v : ℕ → Ω → ℝ) (w : Ω → ℝ)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun j => v j z) atTop (𝓝 (w z)))
    (hb : ∀ j, ∀ᵐ z ∂μ, |v j z| ≤ B ∧ v j z ≤ M) :
    ∀ᵐ z ∂μ, |w z| ≤ B ∧ w z ≤ M := by
  filter_upwards [hlim, ae_all_iff.mpr hb] with z hz hzb
  exact ⟨le_of_tendsto' hz.abs (fun j => (hzb j).1),
    le_of_tendsto' hz (fun j => (hzb j).2)⟩

/-- A finite measure and the literal scalar bound give genuine powered-deficit integrability. -/
theorem auto_deficit_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hFinite : IsFiniteMeasure μ] {M B p : ℝ} (hp : 0 ≤ p)
    (v : Ω → ℝ) (hv : Measurable v)
    (hb : ∀ᵐ z ∂μ, |v z| ≤ B ∧ v z ≤ M) :
    Integrable (fun z => (M-v z)^p) μ := by
  apply (integrable_const ((|M|+B+1)^p)).mono'
  · exact ((Real.continuous_rpow_const hp).measurable.comp
      (measurable_const.sub hv)).aestronglyMeasurable
  · exact hb.mono (fun z hz => auto_deficit_power_bound hp hz.1 hz.2)

/-- Dominated convergence of actual powered deficits on any finite measure, including M < 0. -/
theorem auto_deficit_power_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [hFinite : IsFiniteMeasure μ] {M B p : ℝ}
    (hp : 0 < p) (_hB : 0 ≤ B) (v : ℕ → Ω → ℝ) (w : Ω → ℝ)
    (hv : ∀ j, Measurable (v j)) (hw : Measurable w)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun j => v j z) atTop (𝓝 (w z)))
    (hb : ∀ j, ∀ᵐ z ∂μ, |v j z| ≤ B ∧ v j z ≤ M) :
    (∀ᵐ z ∂μ, 0 ≤ M-w z ∧ |w z| ≤ B) ∧
    (∀ j, Integrable (fun z => (M-v j z)^p) μ) ∧
    Integrable (fun z => (M-w z)^p) μ ∧
    Tendsto (fun j => ∫ z, (M-v j z)^p ∂μ) atTop (𝓝 (∫ z, (M-w z)^p ∂μ)) := by
  have hwBound := auto_deficit_limit_bounds μ v w hlim hb
  refine ⟨hwBound.mono (fun z hz => ⟨sub_nonneg.mpr hz.2, hz.1⟩),
    fun j => auto_deficit_power_integrable μ hp.le (v j) (hv j) (hb j),
    auto_deficit_power_integrable μ hp.le w hw hwBound, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun _ => (|M|+B+1)^p)
  · intro j
    exact ((Real.continuous_rpow_const hp.le).measurable.comp
      (measurable_const.sub (hv j))).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact (hb j).mono (fun z hz => auto_deficit_power_bound hp.le hz.1 hz.2)
  · exact hlim.mono (fun z hz =>
      ((Real.continuous_rpow_const hp.le).tendsto (M-w z)).comp
        (tendsto_const_nhds.sub hz))

end Yau.LeafProofs.L05AutonomousAux
