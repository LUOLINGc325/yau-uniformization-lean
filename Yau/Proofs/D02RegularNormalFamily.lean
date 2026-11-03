import Yau.Proofs.D02AnchoredNormalFamily
import Yau.Proofs.D02AnchorRetention
import Yau.Proofs.D02MorreyExtraction

/-! The original admissible discs have one genuine normal subsequence on
the complement of their actual limiting Riesz atoms. The moving anchors,
the Jacobian potential and the measure retain the same indices. -/

open scoped Topology ContDiff ENNReal CompactlySupported
open MeasureTheory Filter Set Metric

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

theorem discFamily_regular_normal_subsequence {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    letI := L12Aux.inducedMetricSpace X.metric
    ∃ (φ : ℕ → ℕ) (u : ℂ → ℝ) (μ : Measure ℂ)
      (f : C(regularPotentialDomain (ball (0 : ℂ) 1) μ, Pt X)), StrictMono φ ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 →
        IntegrableOn u S volume ∧ Tendsto
          (fun j => ∫ z in S, |immersionPotential X.metric.form F (fs (φ j) z) - u z|) atTop (𝓝 0)) ∧
      (∀ S : Set ℂ, IsCompact S → S ⊆ ball (0 : ℂ) 1 → μ S < ⊤) ∧
      μ (ball (0 : ℂ) 1)ᶜ = 0 ∧
      (∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball (0 : ℂ) 1 →
        (2 * Real.pi) * (∫ z, χ z ∂μ) = ∫ z, u z * LeafCandidates.realPlanarLaplacian χ z) ∧
      (∀ χ : C_c(ℂ, ℝ), tsupport χ ⊆ ball (0 : ℂ) 1 →
        Tendsto (fun j => ∫ z, χ z ∂D02RieszAux.smoothRieszOn (ball (0 : ℂ) 1)
          (fun w => immersionPotential X.metric.form F (fs (φ j) w))) atTop (𝓝 (∫ z, χ z ∂μ))) ∧
      IsOpen (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      IsPathConnected (regularPotentialDomain (ball (0 : ℂ) 1) μ) ∧
      ∀ L : Set (regularPotentialDomain (ball (0 : ℂ) 1) μ), IsCompact L →
        TendstoUniformlyOn (fun j (z : regularPotentialDomain (ball (0 : ℂ) 1) μ) => fs (φ j) z) f atTop L := by
  letI := L12Aux.inducedMetricSpace X.metric
  letI : CompleteSpace (Pt X) := L12Aux.inducedMetricSpace_complete X.metric
  letI : ProperSpace (Pt X) := L12Aux.inducedMetricSpace_proper X.metric
  obtain ⟨α, u, μ, hα, hlocal, hμ, hzero, hdist, hvague, _, ho, hpc, hMorrey⟩ :=
    discFamily_riesz_morrey_subsequence X hF hImm hK A fs hfs
  let O := regularPotentialDomain (ball (0 : ℂ) 1) μ
  let gs : ℕ → ℂ → Pt X := fun j => fs (α j)
  have heq : Equicontinuous (fun j (z : O) => gs j z) := by
    apply equicontinuous_restrict_of_local_holder
    intro x hx
    obtain ⟨r, H, hr, _, hH, hholder⟩ := hMorrey x hx
    exact ⟨r, H, hr, hH, hholder⟩
  obtain ⟨K₁, hK₁, hanchors⟩ := uniform_movingAnchor_compact X.metric hK A
  let S : ℕ → Set ℂ := fun j => anchorAnnulus (goodAngles (discEnergyDensity X.metric.form (gs j)) A)
  have hS (j : ℕ) := hanchors (fs (α j)) (hfs (α j)).1 (hfs (α j)).2.1 (hfs (α j)).2.2
  obtain ⟨H, hH, hHO, hmeet⟩ := exists_compact_regular_anchor_set μ hμ S
    (fun j => ⟨(hS j).2.1, (hS j).2.2.1⟩)
  choose zs hzsS hzsH using hmeet
  obtain ⟨β, hβ, f, hf⟩ := normalFamily_of_moving_anchors hpc.isConnected.isPreconnected gs heq hH hHO
    zs hzsH hK₁ (fun j => (hS j).2.2.2 (zs j) (hzsS j)) ho
  refine ⟨α ∘ β, u, μ, f, hα.comp hβ, ?_, hμ, hzero, hdist, ?_, ho, hpc, ?_⟩
  · intro S hS hSD
    refine ⟨(hlocal S hS hSD).1, ?_⟩
    exact (hlocal S hS hSD).2.comp hβ.tendsto_atTop
  · intro χ hχ
    exact (hvague χ hχ).comp hβ.tendsto_atTop
  · intro L hL
    exact hf L hL

end Yau.NodeProofs.D02Aux
