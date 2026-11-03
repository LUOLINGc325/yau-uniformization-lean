import Yau.Proofs.D02EnergyConvergence

/-! Fatou applies to the actual disc energy densities and the same
holomorphic normal limit. Both the area and the unweighted physical
derivative energy remain finite on the regular domain. -/

open scoped Topology Manifold ContDiff ENNReal
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem normal_limit_area_le {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (hO : IsOpen O) (hOD : O ⊆ ball (0 : ℂ) 1)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hfs : ∀ j, IsHolomorphicDisc (fs j))
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O)
    (A : ℝ) (harea : ∀ j, discArea g.form (fs j) ≤ ENNReal.ofReal A) :
    (∫⁻ z in O, ENNReal.ofReal (curveEnergyDensity g.form f z)) ≤ ENNReal.ofReal A := by
  have hlim : ∀ᵐ z ∂volume.restrict O,
      Tendsto (fun j => discEnergyDensity g.form (fs j) z) atTop
        (𝓝 (ENNReal.ofReal (curveEnergyDensity g.form f z))) := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (curveEnergyDensity_tendsto g hO fs f
        (fun j => (hfs j).mono (hOD.trans ball_subset_closedBall)) hf hconv hz)
    convert ht using 1
    funext j
    rw [discEnergyDensity_eq_physical g.form (hfs j) (hOD hz)]
    rfl
  calc
    _ = ∫⁻ z in O, liminf (fun j => discEnergyDensity g.form (fs j) z) atTop :=
      lintegral_congr_ae (hlim.mono fun z hz => hz.liminf_eq.symm)
    _ ≤ liminf (fun j => ∫⁻ z in O, discEnergyDensity g.form (fs j) z) atTop :=
      lintegral_liminf_le (fun j => discEnergyDensity_measurable g (hfs j))
    _ ≤ ENNReal.ofReal A := liminf_le_of_frequently_le'
      (Eventually.frequently (Eventually.of_forall fun j => by
        calc
          _ ≤ ∫⁻ z in ball (0 : ℂ) 1, discEnergyDensity g.form (fs j) z := lintegral_mono_set hOD
          _ = discArea g.form (fs j) := discEnergyDensity_integral g.form (hfs j)
          _ ≤ ENNReal.ofReal A := harea j))

theorem normal_limit_physical_energy_finite {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (hO : IsOpen O) (hOD : O ⊆ ball (0 : ℂ) 1)
    (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hfs : ∀ j, IsHolomorphicDisc (fs j))
    (hf : ContMDiffOn 𝓘(ℂ, ℂ) (ComplexModel n) ∞ f O)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O)
    (A : ℝ) (harea : ∀ j, discArea g.form (fs j) ≤ ENNReal.ofReal A) :
    (∫⁻ z in O, ENNReal.ofReal (hermitianNormSq (g.form (f z)) (physicalCurveDerivative f z))) < ⊤ := by
  apply lt_of_le_of_lt (b := ENNReal.ofReal A) ?_ ENNReal.ofReal_lt_top
  apply le_trans ?_ (normal_limit_area_le g hO hOD fs f hfs hf hconv A harea)
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  dsimp [curveEnergyDensity]
  linarith [hermitianNormSq_nonneg (g.form (f z)) (physicalCurveDerivative f z)]

theorem normal_limit_continuous_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {O : Set ℂ} (fs : ℕ → ℂ → M.Carrier) (f : ℂ → M.Carrier)
    (hconv : letI := L12Aux.inducedMetricSpace g; TendstoLocallyUniformlyOn fs f atTop O)
    (v : M.Carrier → ℝ) (hv : Continuous v) (B : ℝ)
    (hb : ∀ j z, z ∈ O → v (fs j z) ≤ B) : ∀ z ∈ O, v (f z) ≤ B := by
  letI := L12Aux.inducedMetricSpace g
  intro z hz
  exact le_of_tendsto (hv.continuousAt.tendsto.comp (hconv.tendsto_at hz))
    (Eventually.of_forall fun j => hb j z hz)

end Yau.NodeProofs.D02Aux
