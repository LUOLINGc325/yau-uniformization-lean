import Yau.Proofs.D02RieszDensity
import Yau.Proofs.D02RieszMeasureLimit

open MeasureTheory Filter Set
open scoped Topology ContDiff CompactlySupported

noncomputable section
namespace Yau.NodeProofs.D02RieszAux

/-- Construction of the limiting Riesz measure from the actual smooth
subharmonic sequence and its local L¹ limit. The measure has zero mass outside
`U`; its finiteness is required only on compact subsets of `U`. -/
theorem exists_riesz_measure {U : Set ℂ} (hU : IsOpen U)
    (v : ℕ → ℂ → ℝ) (u : ℂ → ℝ)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) U)
    (hΔ : ∀ j z, z ∈ U → 0 ≤ LeafCandidates.realPlanarLaplacian (v j) z)
    (hu : ∀ K : Set ℂ, IsCompact K → K ⊆ U → IntegrableOn u K volume)
    (hconv : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      Tendsto (fun j ↦ ∫ z in K, |v j z - u z|) atTop (𝓝 0)) :
    ∃ μ : Measure ℂ,
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤) ∧
      μ Uᶜ = 0 ∧
      (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (2 * Real.pi) * (∫ z, φ z ∂μ) =
          ∫ z, u z * LeafCandidates.realPlanarLaplacian φ z) ∧
      (∀ φ : C_c(ℂ, ℝ), tsupport φ ⊆ U →
        Tendsto (fun j ↦ ∫ z, φ z ∂smoothRieszOn U (v j)) atTop
          (𝓝 (∫ z, φ z ∂μ))) := by
  obtain ⟨μ, hμ, hzero, hvague⟩ := exists_measure_of_smooth_pairings hU
    (fun j ↦ smoothRieszOn U (v j))
    (fun j K hK hKU ↦ smoothRieszOn_compact_finite hU (hv j) hK hKU)
    (fun φ hφ hφc hφU ↦ ⟨_, smoothRieszOn_tendsto hU hv hΔ hu hconv hφ hφc hφU⟩)
  refine ⟨μ, hμ, hzero, ?_, hvague⟩
  intro φ hφ hφc hφU
  let φc : C_c(ℂ, ℝ) := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  have heq := tendsto_nhds_unique (hvague φc hφU)
    (smoothRieszOn_tendsto hU hv hΔ hu hconv hφ hφc hφU)
  have hnorm : (∫ z, φ z ∂μ) =
      (∫ z, u z * LeafCandidates.realPlanarLaplacian φ z) / (2 * Real.pi) := heq
  rw [hnorm]
  field_simp

end Yau.NodeProofs.D02RieszAux
