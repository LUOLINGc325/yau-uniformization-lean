import Yau.Proofs.D02RieszGreen
import Yau.Proofs.D02RieszL1

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- The actual normalized smooth Laplacian measure on an open planar domain. -/
def smoothRieszOn (U : Set ℂ) (u : ℂ → ℝ) : Measure ℂ :=
  ((volume : Measure ℂ).withDensity
    (fun z ↦ ENNReal.ofReal (LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi)))).restrict U

theorem smoothRieszOn_compact_finite {U K : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hK : IsCompact K) (hKU : K ⊆ U) :
    smoothRieszOn U u K < ⊤ := by
  let d := fun z ↦ ENNReal.ofReal (LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi))
  have hcont : ContinuousOn (fun z ↦ LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi)) K :=
    ((LeafProofs.L08_contDiffOn_realPlanarLaplacian hU hu).continuousOn.div_const _).mono hKU
  have hi : IntegrableOn (fun z ↦ LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi)) K volume :=
    hcont.integrableOn_compact hK
  letI := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  unfold smoothRieszOn
  rw [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKU]
  have heq : (volume.withDensity d) K = ((volume.restrict K).withDensity d) univ := by
    rw [← restrict_withDensity hK.measurableSet, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  change (volume.withDensity d) K < ⊤
  rw [heq]
  exact measure_lt_top ((volume.restrict K).withDensity d) univ

/-- Integration of a continuous test against the actual smooth density. -/
theorem smoothRieszOn_pairing {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hΔ : ∀ z ∈ U, 0 ≤ LeafCandidates.realPlanarLaplacian u z)
    (hφU : tsupport φ ⊆ U) :
    (∫ z, φ z ∂smoothRieszOn U u) =
      (∫ z, LeafCandidates.realPlanarLaplacian u z * φ z) / (2 * Real.pi) := by
  have hcont := (LeafProofs.L08_contDiffOn_realPlanarLaplacian hU hu).continuousOn.div_const (2 * Real.pi)
  unfold smoothRieszOn
  rw [restrict_withDensity hU.measurableSet,
    integral_withDensity_eq_integral_toReal_smul₀ (hcont.aemeasurable hU.measurableSet).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have heq : (∫ z in U, (ENNReal.ofReal (LeafCandidates.realPlanarLaplacian u z / (2 * Real.pi))).toReal • φ z) =
      ∫ z in U, (LeafCandidates.realPlanarLaplacian u z * φ z) / (2 * Real.pi) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    rw [ENNReal.toReal_ofReal (div_nonneg (hΔ z hz) (by positivity)), smul_eq_mul]
    ring
  rw [heq, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_div _ _
  · intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hφU h)), mul_zero, zero_div]

/-- Exact distributional normalization of the actual smooth measure. -/
theorem smoothRieszOn_Green {U : Set ℂ} (hU : IsOpen U)
    {u φ : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hΔ : ∀ z ∈ U, 0 ≤ LeafCandidates.realPlanarLaplacian u z)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (2 * Real.pi) * (∫ z, φ z ∂smoothRieszOn U u) =
      ∫ z, u z * LeafCandidates.realPlanarLaplacian φ z := by
  rw [smoothRieszOn_pairing hU hu hΔ hφU, integral_laplacian_swap hU hu hφ hφc hφU]
  field_simp

/-- Smooth Riesz pairings converge to the distribution defined by the genuine
locally integrable limit, with the derivatives entirely on the test. -/
theorem smoothRieszOn_tendsto {U : Set ℂ} (hU : IsOpen U)
    {v : ℕ → ℂ → ℝ} {u : ℂ → ℝ}
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hΔ : ∀ j z, z ∈ U → 0 ≤ LeafCandidates.realPlanarLaplacian (v j) z)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ U → IntegrableOn u K volume)
    (hconv : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      Tendsto (fun j ↦ ∫ z in K, |v j z - u z|) atTop (𝓝 0))
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Tendsto (fun j ↦ ∫ z, φ z ∂smoothRieszOn U (v j)) atTop
      (𝓝 ((∫ z, u z * LeafCandidates.realPlanarLaplacian φ z) / (2 * Real.pi))) := by
  let ψ := LeafCandidates.realPlanarLaplacian φ
  have hψ : Continuous ψ := (LeafProofs.L08_contDiff_realPlanarLaplacian hφ).continuous
  have hψc : HasCompactSupport ψ := LeafProofs.L08_hasCompactSupport_realPlanarLaplacian hφ hφc
  have hψU : tsupport ψ ⊆ U := (LeafProofs.L08_tsupport_realPlanarLaplacian_subset hφ).trans hφU
  have hlim := tendsto_pairing_of_Green hψ hψc hψU
    (fun j ↦ ((hv j).continuousOn.mono hψU).integrableOn_compact hψc)
    (hu _ hψc hψU) (hconv _ hψc hψU)
  have hdiv := hlim.div_const (2 * Real.pi)
  apply hdiv.congr'
  apply Filter.Eventually.of_forall
  intro j
  have h := smoothRieszOn_Green hU (hv j) (hΔ j) hφ hφc hφU
  dsimp only [ψ] at *
  symm
  apply (eq_div_iff (by positivity : 2 * Real.pi ≠ 0)).mpr
  simpa only [mul_comm] using h

/-- Restriction to a disc gives exactly the frozen L08 Riesz measure. -/
theorem smoothRieszOn_restrict_ball {U : Set ℂ} {z : ℂ} {r : ℝ}
    (hball : Metric.ball z r ⊆ U) (u : ℂ → ℝ) :
    (smoothRieszOn U u).restrict (Metric.ball z r) = LeafCandidates.smoothRieszMeasure u z r := by
  unfold smoothRieszOn LeafCandidates.smoothRieszMeasure
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hball]

end Yau.NodeProofs.D02RieszAux
